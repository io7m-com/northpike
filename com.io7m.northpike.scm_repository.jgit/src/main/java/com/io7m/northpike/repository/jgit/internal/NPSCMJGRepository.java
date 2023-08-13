/*
 * Copyright © 2023 Mark Raynsford <code@io7m.com> https://www.io7m.com
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR
 * IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */


package com.io7m.northpike.repository.jgit.internal;

import com.io7m.jmulticlose.core.CloseableCollection;
import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.northpike.model.NPCommit;
import com.io7m.northpike.model.NPCommitAuthor;
import com.io7m.northpike.model.NPCommitGraph;
import com.io7m.northpike.model.NPCommitID;
import com.io7m.northpike.model.NPCommitLink;
import com.io7m.northpike.model.NPCommitSummary;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPRepositoryCredentialsNone;
import com.io7m.northpike.model.NPRepositoryCredentialsUsernamePassword;
import com.io7m.northpike.model.NPRepositoryDescription;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.repository.jgit.NPSCMRepositoriesJGit;
import com.io7m.northpike.scm_repository.spi.NPSCMCommitSet;
import com.io7m.northpike.scm_repository.spi.NPSCMEventType;
import com.io7m.northpike.scm_repository.spi.NPSCMRepositoryException;
import com.io7m.northpike.scm_repository.spi.NPSCMRepositoryType;
import com.io7m.northpike.strings.NPStringConstants;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;
import com.io7m.repetoir.core.RPServiceDirectoryType;
import io.opentelemetry.api.trace.Span;
import org.eclipse.jgit.api.ArchiveCommand;
import org.eclipse.jgit.api.Git;
import org.eclipse.jgit.api.errors.GitAPIException;
import org.eclipse.jgit.archive.TgzFormat;
import org.eclipse.jgit.lib.ObjectId;
import org.eclipse.jgit.lib.Ref;
import org.eclipse.jgit.revwalk.RevCommit;
import org.eclipse.jgit.revwalk.RevWalk;
import org.eclipse.jgit.transport.CredentialsProvider;
import org.eclipse.jgit.transport.TagOpt;
import org.eclipse.jgit.transport.UsernamePasswordCredentialsProvider;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.OpenOption;
import java.nio.file.Path;
import java.time.OffsetDateTime;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.Flow;
import java.util.concurrent.SubmissionPublisher;
import java.util.stream.Collectors;

import static com.io7m.northpike.strings.NPStringConstants.ANALYZE;
import static com.io7m.northpike.strings.NPStringConstants.ARCHIVE;
import static com.io7m.northpike.strings.NPStringConstants.CLONE;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_REPOSITORY_WRONG_PROVIDER;
import static com.io7m.northpike.strings.NPStringConstants.GC;
import static com.io7m.northpike.strings.NPStringConstants.PULL;
import static com.io7m.northpike.telemetry.api.NPTelemetryServiceType.recordSpanException;
import static java.nio.file.StandardCopyOption.ATOMIC_MOVE;
import static java.nio.file.StandardCopyOption.REPLACE_EXISTING;
import static java.nio.file.StandardOpenOption.CREATE;
import static java.nio.file.StandardOpenOption.TRUNCATE_EXISTING;
import static java.nio.file.StandardOpenOption.WRITE;
import static java.time.ZoneOffset.UTC;
import static org.eclipse.jgit.lib.SubmoduleConfig.FetchRecurseSubmodulesMode.YES;

/**
 * JGit repository.
 */

public final class NPSCMJGRepository implements NPSCMRepositoryType
{
  private static final OpenOption[] TEMPORARY_FILE_OPTIONS =
    {TRUNCATE_EXISTING, CREATE, WRITE};

  private final NPStrings strings;
  private final NPTelemetryServiceType telemetry;
  private final NPRepositoryDescription repositoryDescription;
  private final Path repoPath;
  private final HashMap<String, String> attributes;
  private final SubmissionPublisher<NPSCMEventType> events;
  private Git git;
  private final CloseableCollectionType<NPSCMRepositoryException> resources;

  private NPSCMJGRepository(
    final NPStrings inStrings,
    final NPTelemetryServiceType inTelemetry,
    final NPRepositoryDescription inDescription,
    final Path inRepoPath)
  {
    this.strings =
      Objects.requireNonNull(inStrings, "strings");
    this.telemetry =
      Objects.requireNonNull(inTelemetry, "telemetry");
    this.repositoryDescription =
      Objects.requireNonNull(inDescription, "description");
    this.repoPath =
      Objects.requireNonNull(inRepoPath, "repoPath");
    this.attributes =
      new HashMap<>();
    this.resources =
      CloseableCollection.create(() -> {
        return new NPSCMRepositoryException(
          "One or more resources could not be closed.",
          new NPErrorCode("resource"),
          Map.of(),
          Optional.empty()
        );
      });
    this.events =
      this.resources.add(new SubmissionPublisher<>());
  }

  /**
   * Create a new repository instance.
   *
   * @param services      The service directory
   * @param dataDirectory The directory used to store repository data
   * @param repository    The repository
   *
   * @return A new instance
   *
   * @throws NPSCMRepositoryException On errors
   */

  public static NPSCMRepositoryType create(
    final RPServiceDirectoryType services,
    final Path dataDirectory,
    final NPRepositoryDescription repository)
    throws NPSCMRepositoryException
  {
    final var strings =
      services.requireService(NPStrings.class);
    final var telemetry =
      services.requireService(NPTelemetryServiceType.class);

    final var expected =
      NPSCMRepositoriesJGit.providerNameGet();
    final var received =
      repository.provider();

    if (!Objects.equals(received, expected)) {
      throw new NPSCMRepositoryException(
        strings.format(ERROR_REPOSITORY_WRONG_PROVIDER),
        NPStandardErrorCodes.errorApiMisuse(),
        Map.of(),
        Optional.empty()
      );
    }

    final var scmDirectory =
      dataDirectory.resolve(expected.value());
    final var repos =
      scmDirectory.resolve(repository.id() + ".git");

    return new NPSCMJGRepository(
      strings,
      telemetry,
      repository,
      repos
    );
  }

  private static HashSet<NPCommitLink> processCommitLinks(
    final HashMap<String, NPCommit> commitsById,
    final ArrayList<Map.Entry<String, String>> commitLinks)
  {
    final var createdLinks = new HashSet<NPCommitLink>();
    for (final var link : commitLinks) {
      final var parent =
        commitsById.get(link.getKey());
      final var child =
        commitsById.get(link.getValue());

      if (parent != null) {
        if (child != null) {
          createdLinks.add(
            new NPCommitLink(parent.id(), Optional.of(child.id()))
          );
        } else {
          createdLinks.add(
            new NPCommitLink(parent.id(), Optional.empty())
          );
        }
      }
    }
    return createdLinks;
  }

  @Override
  public NPRepositoryDescription description()
  {
    return this.repositoryDescription;
  }

  @Override
  public Flow.Publisher<NPSCMEventType> events()
  {
    return this.events;
  }

  @Override
  public NPSCMCommitSet commitsSince(
    final Set<NPCommitSummary> commits)
    throws NPSCMRepositoryException
  {
    Objects.requireNonNull(commits, "commits");

    final var span =
      this.telemetry.tracer()
        .spanBuilder("CommitsSince")
        .startSpan();

    try (var ignored = span.makeCurrent()) {
      this.ensureRepository();
      return this.executeCalculateSince(commits);
    } finally {
      span.end();
    }
  }

  private void ensureRepository()
    throws NPSCMRepositoryException
  {
    this.setupAttributes();
    if (!Files.isDirectory(this.repoPath)) {
      this.executeClone();
    }
    this.executeUpdate();
  }

  @Override
  public void commitArchive(
    final NPCommitID commit,
    final Path outputFile,
    final Path outputFileTmp)
    throws NPSCMRepositoryException
  {
    Objects.requireNonNull(commit, "commit");
    Objects.requireNonNull(outputFile, "outputFile");
    Objects.requireNonNull(outputFileTmp, "outputFileTmp");

    final var span =
      this.telemetry.tracer()
        .spanBuilder("Archive")
        .startSpan();

    try (var ignored0 = span.makeCurrent()) {
      this.ensureRepository();

      ArchiveCommand.registerFormat("tar.gz", new TgzFormat());
      final var task = new NPSCMJTask(this.events, ARCHIVE);

      try {
        try (var output =
               Files.newOutputStream(outputFileTmp, TEMPORARY_FILE_OPTIONS)) {

          try (var out =
                 this.git.archive()
                   .setFormat("tar.gz")
                   .setOutputStream(output)
                   .setTree(ObjectId.fromString(commit.value()))
                   .call()) {
            out.flush();
          }
        }

        Files.move(outputFileTmp, outputFile, REPLACE_EXISTING, ATOMIC_MOVE);
        task.onCompleted();
      } catch (final Exception e) {
        recordSpanException(e);
        final var ex = this.handleException(e);
        task.onFailed(ex);
        throw ex;
      }
    } finally {
      span.end();
    }
  }

  private NPSCMCommitSet executeCalculateSince(
    final Set<NPCommitSummary> commits)
    throws NPSCMRepositoryException
  {
    final var span =
      this.telemetry.tracer()
        .spanBuilder("Analyze")
        .startSpan();

    try (var ignored = span.makeCurrent()) {
      final var task = new NPSCMJTask(this.events, ANALYZE);
      try {
        task.beginTask(null, commits.size());

        final var repositoryInstance =
          this.git.getRepository();

        final var commitsById =
          new HashMap<String, NPCommit>();
        final var commitLinks =
          new ArrayList<Map.Entry<String, String>>();

        final var allRefs =
          repositoryInstance.getRefDatabase()
            .getRefs();

        try (var revWalker = new RevWalk(repositoryInstance)) {

          /*
           * Start traversal at all the head commits.
           */

          for (final var ref : allRefs) {
            revWalker.markStart(revWalker.parseCommit(ref.getObjectId()));
          }

          /*
           * Mark all the given commits as "uninteresting". This ensures that
           * graph traversal will go as far as those commits but no further,
           * and the commits themselves will not be processed.
           */

          for (final var endCommit : commits) {
            revWalker.markUninteresting(
              revWalker.parseCommit(ObjectId.fromString(endCommit.id().value()))
            );
          }

          this.processCommits(commitsById, commitLinks, revWalker);
        }
        task.update(1);

        final var createdLinks =
          processCommitLinks(commitsById, commitLinks);

        task.onCompleted();
        return new NPSCMCommitSet(
          Set.copyOf(commitsById.values()),
          NPCommitGraph.create(createdLinks)
        );
      } catch (final Exception e) {
        recordSpanException(e);
        final var ex = this.handleException(e);
        task.onFailed(ex);
        throw ex;
      }
    } finally {
      span.end();
    }
  }

  private void processCommits(
    final HashMap<String, NPCommit> commitsById,
    final ArrayList<Map.Entry<String, String>> commitLinks,
    final RevWalk revWalker)
    throws GitAPIException, IOException
  {
    for (final var walkCommit : revWalker) {
      for (var index = 0; index < walkCommit.getParentCount(); ++index) {
        commitLinks.add(Map.entry(
          walkCommit.name(),
          walkCommit.getParent(index).name()
        ));
      }

      final var result = this.transformCommit(walkCommit);
      commitsById.put(walkCommit.name(), result);
    }
  }

  private NPCommit transformCommit(
    final RevCommit source)
    throws GitAPIException, IOException
  {
    final var ident =
      source.getAuthorIdent();

    final var commitObjectId =
      ObjectId.fromString(source.name());

    final var branches =
      Set.copyOf(
        this.git.nameRev()
          .addPrefix("refs/heads")
          .add(commitObjectId)
          .call()
          .values()
      );

    final var timeCreated =
      OffsetDateTime.ofInstant(
        ident.getWhenAsInstant(),
        ident.getZoneId()
      );

    final var timeCreatedUTC =
      timeCreated.atZoneSameInstant(UTC)
        .toOffsetDateTime();

    final var timeReceived =
      OffsetDateTime.now(UTC);

    final var tagList =
      this.git.tagList()
        .setContains(commitObjectId)
        .call();

    final var tags =
      tagList.stream()
        .map(Ref::getName)
        .collect(Collectors.toUnmodifiableSet());

    final var author =
      new NPCommitAuthor(
        ident.getName(),
        ident.getEmailAddress()
      );

    return new NPCommit(
      new NPCommitID(
        this.repositoryDescription.id(),
        source.name()
      ),
      timeCreatedUTC,
      timeReceived,
      author,
      source.getShortMessage(),
      source.getFullMessage(),
      branches,
      tags
    );
  }

  private void executeUpdate()
    throws NPSCMRepositoryException
  {
    final var span =
      this.telemetry.tracer()
        .spanBuilder("Update")
        .startSpan();

    try (var ignored = span.makeCurrent()) {
      this.executeUpdatePull();
      this.executeUpdateGC();
    } finally {
      span.end();
    }
  }

  private void executeUpdateGC()
    throws NPSCMRepositoryException
  {
    final var span =
      this.telemetry.tracer()
        .spanBuilder("RepositoryGC")
        .startSpan();

    try (var ignored = span.makeCurrent()) {
      final var task = new NPSCMJTask(this.events, GC);
      try {
        this.git.gc()
          .setAggressive(true)
          .setProgressMonitor(task)
          .call();
        task.onCompleted();
      } catch (final Exception e) {
        recordSpanException(e);
        final var ex = this.handleException(e);
        task.onFailed(ex);
        throw ex;
      }
    } finally {
      span.end();
    }
  }

  private void executeUpdatePull()
    throws NPSCMRepositoryException
  {
    final var span =
      this.telemetry.tracer()
        .spanBuilder("Pull")
        .startSpan();

    try (var ignored = span.makeCurrent()) {
      final var task = new NPSCMJTask(this.events, PULL);
      try {
        this.git = this.resources.add(Git.open(this.repoPath.toFile()));
        this.git.fetch()
          .setCredentialsProvider(this.createCredentialsProvider())
          .setProgressMonitor(task)
          .setRecurseSubmodules(YES)
          .call();
        task.onCompleted();
      } catch (final Exception e) {
        recordSpanException(e);
        final var ex = this.handleException(e);
        task.onFailed(ex);
        throw ex;
      }
    } finally {
      span.end();
    }
  }

  private NPSCMRepositoryException handleException(
    final Exception e)
  {
    return new NPSCMRepositoryException(
      e.getMessage(),
      e,
      NPStandardErrorCodes.errorIo(),
      Map.copyOf(this.attributes),
      Optional.empty()
    );
  }

  private void setupAttributes()
  {
    this.attributes.clear();
    this.setupAttribute(
      this.strings.format(NPStringConstants.REPOSITORY),
      this.repositoryDescription.id().toString()
    );
  }

  private void setupAttribute(
    final String key,
    final String val)
  {
    this.attributes.put(key, val);
    Span.current().setAttribute(key, val);
  }

  private void executeClone()
    throws NPSCMRepositoryException
  {
    final var span =
      this.telemetry.tracer()
        .spanBuilder("Clone")
        .startSpan();

    try (var ignored = span.makeCurrent()) {
      final var task = new NPSCMJTask(this.events, CLONE);
      try {
        this.git =
          this.resources.add(
            Git.cloneRepository()
              .setBare(true)
              .setCloneAllBranches(true)
              .setTagOption(TagOpt.FETCH_TAGS)
              .setGitDir(this.repoPath.toFile())
              .setMirror(true)
              .setURI(this.repositoryDescription.url().normalize().toString())
              .setCredentialsProvider(this.createCredentialsProvider())
              .setProgressMonitor(task)
              .setCloneSubmodules(true)
              .call()
          );

        task.onCompleted();
      } catch (final Exception e) {
        recordSpanException(e);
        final var ex = this.handleException(e);
        task.onFailed(ex);
        throw ex;
      }
    } finally {
      span.end();
    }
  }

  private CredentialsProvider createCredentialsProvider()
  {
    if (this.repositoryDescription.credentials()
      instanceof final NPRepositoryCredentialsUsernamePassword creds) {
      return new UsernamePasswordCredentialsProvider(
        creds.userName(),
        creds.password()
      );
    }

    if (this.repositoryDescription.credentials()
      instanceof NPRepositoryCredentialsNone) {
      return new NPSCMJGCredentialsNone();
    }

    throw new IllegalStateException();
  }

  @Override
  public void close()
    throws NPSCMRepositoryException
  {
    this.resources.close();
  }
}
