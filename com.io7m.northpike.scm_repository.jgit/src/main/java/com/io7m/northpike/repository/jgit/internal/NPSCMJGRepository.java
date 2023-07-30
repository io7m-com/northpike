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

import com.io7m.northpike.model.NPCommit;
import com.io7m.northpike.model.NPCommitAuthor;
import com.io7m.northpike.model.NPCommitGraph;
import com.io7m.northpike.model.NPCommitID;
import com.io7m.northpike.model.NPCommitLink;
import com.io7m.northpike.model.NPCommitSummary;
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
import com.io7m.repetoir.core.RPServiceDirectoryType;
import org.eclipse.jgit.api.Git;
import org.eclipse.jgit.api.errors.GitAPIException;
import org.eclipse.jgit.lib.ObjectId;
import org.eclipse.jgit.lib.Ref;
import org.eclipse.jgit.revwalk.RevCommit;
import org.eclipse.jgit.revwalk.RevWalk;
import org.eclipse.jgit.transport.CredentialsProvider;
import org.eclipse.jgit.transport.TagOpt;
import org.eclipse.jgit.transport.UsernamePasswordCredentialsProvider;

import java.io.IOException;
import java.nio.file.Files;
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
import static com.io7m.northpike.strings.NPStringConstants.CLONE;
import static com.io7m.northpike.strings.NPStringConstants.GC;
import static com.io7m.northpike.strings.NPStringConstants.PULL;
import static java.time.ZoneOffset.UTC;

/**
 * JGit repository.
 */

public final class NPSCMJGRepository implements NPSCMRepositoryType
{
  private final NPStrings strings;
  private final NPRepositoryDescription repositoryDescription;
  private final Path repoPath;
  private final HashMap<String, String> attributes;
  private final SubmissionPublisher<NPSCMEventType> events;
  private Git git;

  private NPSCMJGRepository(
    final NPStrings inStrings,
    final NPRepositoryDescription inDescription,
    final Path inRepoPath)
  {
    this.strings =
      Objects.requireNonNull(inStrings, "strings");
    this.repositoryDescription =
      Objects.requireNonNull(inDescription, "description");
    this.repoPath =
      Objects.requireNonNull(inRepoPath, "repoPath");
    this.attributes =
      new HashMap<>();
    this.events =
      new SubmissionPublisher<>();
  }

  /**
   * Create a new repository instance.
   *
   * @param services      The service directory
   * @param dataDirectory The directory used to store repository data
   * @param repository    The repository
   *
   * @return A new instance
   */

  public static NPSCMRepositoryType create(
    final RPServiceDirectoryType services,
    final Path dataDirectory,
    final NPRepositoryDescription repository)
  {
    final var strings =
      services.requireService(NPStrings.class);

    final var expected =
      NPSCMRepositoriesJGit.providerNameGet();
    final var received =
      repository.provider();

    if (!Objects.equals(received, expected)) {
      throw new IllegalStateException();
    }

    final var scmDirectory =
      dataDirectory.resolve(expected.value());
    final var repos =
      scmDirectory.resolve(repository.id() + ".git");
    return new NPSCMJGRepository(strings, repository, repos);
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
    this.setupAttributes();

    if (!Files.isDirectory(this.repoPath)) {
      this.executeClone();
    }

    this.executeUpdate();
    return this.executeCalculateSince(commits);
  }

  private NPSCMCommitSet executeCalculateSince(
    final Set<NPCommitSummary> commits)
    throws NPSCMRepositoryException
  {
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
      final var ex = this.handleException(e);
      task.onFailed(ex);
      throw ex;
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
    final var task0 = new NPSCMJTask(this.events, PULL);
    try {
      this.git = Git.open(this.repoPath.toFile());
      this.git.fetch()
        .setCredentialsProvider(this.createCredentialsProvider())
        .setProgressMonitor(task0)
        .call();
      task0.onCompleted();
    } catch (final Exception e) {
      final var ex = this.handleException(e);
      task0.onFailed(ex);
      throw ex;
    }

    final var task1 = new NPSCMJTask(this.events, GC);
    try {
      this.git.gc()
        .setAggressive(true)
        .setProgressMonitor(task1)
        .call();
      task1.onCompleted();
    } catch (final Exception e) {
      final var ex = this.handleException(e);
      task1.onFailed(ex);
      throw ex;
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
    this.attributes.put(
      this.strings.format(NPStringConstants.REPOSITORY),
      this.repositoryDescription.id().toString()
    );
  }

  private void executeClone()
    throws NPSCMRepositoryException
  {
    final var task = new NPSCMJTask(this.events, CLONE);
    try {
      this.git =
        Git.cloneRepository()
          .setBare(true)
          .setCloneAllBranches(true)
          .setTagOption(TagOpt.FETCH_TAGS)
          .setGitDir(this.repoPath.toFile())
          .setMirror(true)
          .setURI(this.repositoryDescription.url().normalize().toString())
          .setCredentialsProvider(this.createCredentialsProvider())
          .setProgressMonitor(task)
          .call();

      task.onCompleted();
    } catch (final Exception e) {
      final var ex = this.handleException(e);
      task.onFailed(ex);
      throw ex;
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
  {
    this.events.close();
  }
}
