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


package com.io7m.northpike.scm_repository.spi;

import com.io7m.northpike.model.NPCommitID;
import com.io7m.northpike.model.NPCommitSummary;
import com.io7m.northpike.model.NPRepositoryDescription;

import java.nio.file.Path;
import java.time.OffsetDateTime;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.Flow;

/**
 * An SCM repository instance.
 */

public interface NPSCMRepositoryType extends AutoCloseable
{
  /**
   * @return The description of the repository
   */

  NPRepositoryDescription description();

  /**
   * @return The repository events
   */

  Flow.Publisher<NPSCMEventType> events();

  /**
   * Determine the set of commits that have been created since the creation
   * of the given set of commits. If an empty set is passed in, all commits
   * will be returned.
   *
   * @param commits The set of initial commits
   *
   * @return The set of new commits
   *
   * @throws NPSCMRepositoryException On errors
   */

  NPSCMCommitSet commitsSince(
    Set<NPCommitSummary> commits)
    throws NPSCMRepositoryException;

  /**
   * Produce an archive of the given commit as a compressed tarball.
   *
   * @param commit        The commit
   * @param outputFile    The output file
   * @param outputFileTmp The temporary output file
   *
   * @throws NPSCMRepositoryException On errors
   */

  void commitArchive(
    NPCommitID commit,
    Path outputFile,
    Path outputFileTmp)
    throws NPSCMRepositoryException;

  @Override
  void close()
    throws NPSCMRepositoryException;

  /**
   * Determine the set of commits that have been received since the given
   * received time. If no time is passed in, all commits will be returned.
   *
   * @param since The last received time
   *
   * @return The set of new commits
   *
   * @throws NPSCMRepositoryException On errors
   */

  NPSCMCommitSet commitsSinceTime(
    Optional<OffsetDateTime> since)
    throws NPSCMRepositoryException;
}
