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
import com.io7m.northpike.clock.NPClockServiceType;
import com.io7m.northpike.keys.NPSignatureKeyLookupType;
import com.io7m.northpike.model.NPArchive;
import com.io7m.northpike.model.NPCommit;
import com.io7m.northpike.model.NPCommitAuthor;
import com.io7m.northpike.model.NPCommitGraph;
import com.io7m.northpike.model.NPCommitID;
import com.io7m.northpike.model.NPCommitLink;
import com.io7m.northpike.model.NPCommitSummary;
import com.io7m.northpike.model.NPCommitUnqualifiedID;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPFingerprint;
import com.io7m.northpike.model.NPHash;
import com.io7m.northpike.model.NPRepositoryCredentialsNone;
import com.io7m.northpike.model.NPRepositoryCredentialsUsernamePassword;
import com.io7m.northpike.model.NPRepositoryDescription;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.model.NPToken;
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
import org.eclipse.jgit.api.ListBranchCommand;
import org.eclipse.jgit.api.VerifySignatureCommand;
import org.eclipse.jgit.api.errors.GitAPIException;
import org.eclipse.jgit.archive.TgzFormat;
import org.eclipse.jgit.lib.Constants;
import org.eclipse.jgit.lib.ObjectId;
import org.eclipse.jgit.lib.Ref;
import org.eclipse.jgit.revwalk.RevCommit;
import org.eclipse.jgit.revwalk.RevSort;
import org.eclipse.jgit.revwalk.RevWalk;
import org.eclipse.jgit.revwalk.filter.CommitTimeRevFilter;
import org.eclipse.jgit.transport.CredentialsProvider;
import org.eclipse.jgit.transport.TagOpt;
import org.eclipse.jgit.transport.UsernamePasswordCredentialsProvider;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.OpenOption;
import java.nio.file.Path;
import java.security.DigestOutputStream;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.time.OffsetDateTime;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.HexFormat;
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
import static com.io7m.northpike.strings.NPStringConstants.VERIFY;
import static com.io7m.northpike.telemetry.api.NPTelemetryServiceType.recordSpanException;
import static java.nio.file.StandardCopyOption.ATOMIC_MOVE;
import static java.nio.file.StandardCopyOption.REPLACE_EXISTING;
import static java.nio.file.StandardOpenOption.CREATE;
import static java.nio.file.StandardOpenOption.TRUNCATE_EXISTING;
import static java.nio.file.StandardOpenOption.WRITE;
import static java.time.ZoneOffset.UTC;
import static org.eclipse.jgit.api.VerifySignatureCommand.VerifyMode.ANY;
import static org.eclipse.jgit.lib.SubmoduleConfig.FetchRecurseSubmodulesMode.YES;

/**
 * JGit repository.
 */

public final class NPSCMJGRepository implements NPSCMRepositoryType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPSCMJGRepository.class);

  private static final OpenOption[] TEMPORARY_FILE_OPTIONS =
    {TRUNCATE_EXISTING, CREATE, WRITE};

  private final NPStrings strings;
  private final NPClockServiceType clock;
  private final NPTelemetryServiceType telemetry;
  private final NPRepositoryDescription repositoryDescription;
  private final Path repoPath;
  private final HashMap<String, String> attributes;
  private final SubmissionPublisher<NPSCMEventType> events;
  private final CloseableCollectionType<NPSCMRepositoryException> resources;
  private Git git;

  private NPSCMJGRepository(
    final NPStrings inStrings,
    final NPClockServiceType inClock,
    final NPTelemetryServiceType inTelemetry,
    final NPRepositoryDescription inDescription,
    final Path inRepoPath)
  {
    this.strings =
      Objects.requireNonNull(inStrings, "strings");
    this.clock =
      Objects.requireNonNull(inClock, "inClock");
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
      services.requireService(NPClockServiceType.class),
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
  public NPArchive commitArchive(
    final NPCommitID commit,
    final NPToken token,
    final Path outputFile,
    final Path outputFileTmp,
    final Path checksumOutputFile,
    final Path checksumOutputFileTmp)
    throws NPSCMRepositoryException
  {
    Objects.requireNonNull(commit, "commit");
    Objects.requireNonNull(token, "token");
    Objects.requireNonNull(outputFile, "outputFile");
    Objects.requireNonNull(outputFileTmp, "outputFileTmp");
    Objects.requireNonNull(checksumOutputFile, "checksumOutputFile");
    Objects.requireNonNull(checksumOutputFileTmp, "checksumOutputFileTmp");

    final var span =
      this.telemetry.tracer()
        .spanBuilder("Archive")
        .startSpan();

    try (var ignored0 = span.makeCurrent()) {
      this.ensureRepository();

      ArchiveCommand.registerFormat("tar.gz", new TgzFormat());
      final var task = new NPSCMJTask(this.events, ARCHIVE);

      try {
        Files.createDirectories(outputFile.getParent());
        Files.createDirectories(outputFileTmp.getParent());
        Files.createDirectories(checksumOutputFile.getParent());
        Files.createDirectories(checksumOutputFileTmp.getParent());

        try (var output =
               Files.newOutputStream(outputFileTmp, TEMPORARY_FILE_OPTIONS)) {

          try (var out =
                 this.git.archive()
                   .setFormat("tar.gz")
                   .setOutputStream(output)
                   .setTree(ObjectId.fromString(commit.commitId().value()))
                   .call()) {
            out.flush();
          }
        }

        final var hash = sha256Of(outputFileTmp);

        Files.writeString(
          checksumOutputFileTmp,
          hash,
          StandardCharsets.UTF_8,
          CREATE,
          TRUNCATE_EXISTING,
          WRITE
        );
        Files.move(
          checksumOutputFileTmp,
          checksumOutputFile,
          REPLACE_EXISTING,
          ATOMIC_MOVE
        );
        Files.move(
          outputFileTmp,
          outputFile,
          REPLACE_EXISTING,
          ATOMIC_MOVE
        );

        task.onCompleted();
        return new NPArchive(
          token,
          commit,
          new NPHash("SHA-256", hash),
          OffsetDateTime.now()
        );
      } catch (final Exception e) {
        recordSpanException(e);
        LOG.error("commitArchive: ", e);
        final var ex = this.handleException(e);
        task.onFailed(ex);
        throw ex;
      }
    } finally {
      span.end();
    }
  }

  private static String sha256Of(
    final Path file)
    throws NoSuchAlgorithmException, IOException
  {
    final var digest =
      MessageDigest.getInstance("SHA-256");

    final var nullOut = OutputStream.nullOutputStream();
    try (var outputStream = new DigestOutputStream(nullOut, digest)) {
      try (var inputStream = Files.newInputStream(file)) {
        inputStream.transferTo(outputStream);
      }
    }
    return HexFormat.of().withLowerCase().formatHex(digest.digest());
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
              revWalker.parseCommit(
                ObjectId.fromString(endCommit.id().commitId().value())
              )
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
        LOG.error("executeCalculateSince: ", e);
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

    final var branches =
      this.transformGetBranchesForCommit(source);

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

    final var tags =
      this.transformGetTagsForCommit(source);

    final var author =
      new NPCommitAuthor(
        ident.getName(),
        ident.getEmailAddress()
      );

    return new NPCommit(
      new NPCommitID(
        this.repositoryDescription.id(),
        new NPCommitUnqualifiedID(source.name())
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

  private Set<String> transformGetBranchesForCommit(
    final RevCommit source)
    throws GitAPIException
  {
    return this.git.branchList()
      .setContains(source.name())
      .setListMode(ListBranchCommand.ListMode.ALL)
      .call()
      .stream()
      .map(Ref::getName)
      .map(s -> s.replace("refs/heads/", ""))
      .collect(Collectors.toSet());
  }

  private Set<String> transformGetTagsForCommit(
    final RevCommit source)
    throws GitAPIException
  {
    final var tagList =
      this.git.tagList()
        .call();

    final var tagNames = new HashSet<String>();
    for (final var ref : tagList) {
      final var peeledRef = ref.getPeeledObjectId();
      if (Objects.equals(peeledRef, source.toObjectId())) {
        tagNames.add(ref.getName().replace("refs/tags/", ""));
      }
    }

    return Set.copyOf(tagNames);
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
        LOG.error("executeUpdateGC: ", e);
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
        this.git = this.exchangeGit(Git.open(this.repoPath.toFile()));
        this.git.fetch()
          .setCredentialsProvider(this.createCredentialsProvider())
          .setProgressMonitor(task)
          .setRecurseSubmodules(YES)
          .call();
        task.onCompleted();
      } catch (final Exception e) {
        recordSpanException(e);
        LOG.error("executeUpdatePull: ", e);
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
          this.exchangeGit(
            Git.cloneRepository()
              .setBare(true)
              .setCloneAllBranches(true)
              .setCloneSubmodules(true)
              .setCredentialsProvider(this.createCredentialsProvider())
              .setGitDir(this.repoPath.toFile())
              .setMirror(true)
              .setProgressMonitor(task)
              .setTagOption(TagOpt.FETCH_TAGS)
              .setURI(this.repositoryDescription.url().normalize().toString())
              .call()
          );

        task.onCompleted();
      } catch (final Exception e) {
        recordSpanException(e);
        LOG.error("executeClone: ", e);
        final var ex = this.handleException(e);
        task.onFailed(ex);
        throw ex;
      }
    } finally {
      span.end();
    }
  }

  private Git exchangeGit(
    final Git newGit)
  {
    final var oldGit = this.git;
    if (oldGit != null) {
      oldGit.close();
    }
    this.git = this.resources.add(newGit);
    return this.git;
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

  @Override
  public NPSCMCommitSet commitsSinceTime(
    final Optional<OffsetDateTime> since)
    throws NPSCMRepositoryException
  {
    Objects.requireNonNull(since, "since");

    final var span =
      this.telemetry.tracer()
        .spanBuilder("CommitsReceivedSinceTime")
        .startSpan();

    try (var ignored = span.makeCurrent()) {
      this.ensureRepository();
      return this.executeCalculateSinceTime(since);
    } finally {
      span.end();
    }
  }

  @Override
  public NPFingerprint commitVerifySignature(
    final NPCommitUnqualifiedID commit,
    final NPSignatureKeyLookupType keys)
    throws NPSCMRepositoryException
  {
    Objects.requireNonNull(commit, "commit");
    Objects.requireNonNull(keys, "keys");

    final var span =
      this.telemetry.tracer()
        .spanBuilder("VerifyCommit")
        .startSpan();

    try (var ignored = span.makeCurrent()) {
      final var task = new NPSCMJTask(this.events, VERIFY);
      try {
        this.ensureRepository();

        final var repository =
          this.git.getRepository();

        final var verifier =
          new NPSCMJGVerifier(commit, keys, this.clock);

        new VerifySignatureCommand(repository)
          .addName(commit.value())
          .setMode(ANY)
          .setVerifier(verifier)
          .call();

        task.onCompleted();
        return verifier.keyUsed().fingerprint();
      } catch (final Exception e) {
        recordSpanException(e);
        LOG.error("commitVerifySignature: ", e);
        final var ex = this.handleException(e);
        task.onFailed(ex);
        throw ex;
      }
    } finally {
      span.end();
    }
  }

  private NPSCMCommitSet executeCalculateSinceTime(
    final Optional<OffsetDateTime> since)
    throws NPSCMRepositoryException
  {
    final var span =
      this.telemetry.tracer()
        .spanBuilder("Analyze")
        .startSpan();

    try (var ignored = span.makeCurrent()) {
      final var task = new NPSCMJTask(this.events, ANALYZE);
      try {
        task.beginTask(null, 0);

        final var repositoryInstance =
          this.git.getRepository();

        final var commitsById =
          new HashMap<String, NPCommit>();
        final var commitLinks =
          new ArrayList<Map.Entry<String, String>>();

        try (var walk = new RevWalk(repositoryInstance)) {
          walk.markStart(walk.parseCommit(repositoryInstance.resolve(Constants.HEAD)));
          walk.sort(RevSort.REVERSE);

          since.ifPresent(time -> {
            walk.setRevFilter(CommitTimeRevFilter.after(
              time.toInstant().toEpochMilli() - 1000L
            ));
          });

          this.processCommits(commitsById, commitLinks, walk);
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
        LOG.error("executeCalculateSinceTime: ", e);
        final var ex = this.handleException(e);
        task.onFailed(ex);
        throw ex;
      }
    } finally {
      span.end();
    }
  }
}
