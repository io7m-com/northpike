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

package com.io7m.northpike.database.api;


import com.io7m.northpike.model.NPCommit;
import com.io7m.northpike.model.NPCommitGraph;
import com.io7m.northpike.model.NPCommitID;
import com.io7m.northpike.model.NPCommitSearchParameters;
import com.io7m.northpike.model.NPCommitSummary;
import com.io7m.northpike.model.NPFingerprint;
import com.io7m.northpike.model.NPRepositoryDescription;
import com.io7m.northpike.model.NPRepositoryID;

import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * The database queries involving repositories.
 */

public sealed interface NPDatabaseQueriesRepositoriesType
  extends NPDatabaseQueriesType
{
  /**
   * Update the given repository.
   */

  non-sealed interface RepositoryPutType
    extends NPDatabaseQueryType<NPRepositoryDescription, NPDatabaseUnit>,
    NPDatabaseQueriesRepositoriesType
  {

  }

  /**
   * Retrieve a repository.
   */

  non-sealed interface RepositoryGetType
    extends NPDatabaseQueryType<NPRepositoryID, Optional<NPRepositoryDescription>>,
    NPDatabaseQueriesRepositoriesType
  {

  }

  /**
   * List repositories.
   */

  non-sealed interface RepositoryListType
    extends NPDatabaseQueryType<NPDatabaseUnit, NPRepositoriesPagedType>,
    NPDatabaseQueriesRepositoriesType
  {

  }

  /**
   * Add or update commits in the given repository.
   */

  non-sealed interface RepositoryCommitsPutType
    extends NPDatabaseQueryType<RepositoryCommitsPutType.Parameters, NPDatabaseUnit>,
    NPDatabaseQueriesRepositoriesType
  {
    /**
     * The commit parameters.
     *
     * @param commits     The set of commits
     * @param commitGraph The commit graph
     */

    record Parameters(
      Set<NPCommit> commits,
      NPCommitGraph commitGraph)
    {
      /**
       * The commit parameters.
       */

      public Parameters
      {
        Objects.requireNonNull(commits, "commits");
        Objects.requireNonNull(commitGraph, "commitGraph");
      }
    }
  }

  /**
   * Get a commit from a repository.
   */

  non-sealed interface RepositoryCommitGetType
    extends NPDatabaseQueryType<NPCommitID, Optional<NPCommit>>,
    NPDatabaseQueriesRepositoriesType
  {

  }

  /**
   * List commits in the repository.
   */

  non-sealed interface RepositoryCommitsGetType
    extends NPDatabaseQueryType<NPCommitSearchParameters, NPCommitSummaryLinkedPagedType>,
    NPDatabaseQueriesRepositoriesType
  {

  }

  /**
   * Get the most recently received commit in the repository.
   */

  non-sealed interface RepositoryCommitsGetMostRecentlyReceivedType
    extends NPDatabaseQueryType<NPRepositoryID, Optional<NPCommitSummary>>,
    NPDatabaseQueriesRepositoriesType
  {

  }

  /**
   * Assign a key to a repository.
   */

  non-sealed interface RepositoryPublicKeyAssignType
    extends NPDatabaseQueryType<RepositoryPublicKeyAssignType.Parameters, NPDatabaseUnit>,
    NPDatabaseQueriesRepositoriesType
  {
    /**
     * The parameters.
     *
     * @param repositoryId The repository
     * @param key          The key
     */

    record Parameters(
      NPRepositoryID repositoryId,
      NPFingerprint key)
    {
      /**
       * The parameters.
       */

      public Parameters
      {
        Objects.requireNonNull(repositoryId, "repositoryId");
        Objects.requireNonNull(key, "key");
      }
    }
  }

  /**
   * Unassign a key from a repository.
   */

  non-sealed interface RepositoryPublicKeyUnassignType
    extends NPDatabaseQueryType<RepositoryPublicKeyUnassignType.Parameters, NPDatabaseUnit>,
    NPDatabaseQueriesRepositoriesType
  {
    /**
     * The parameters.
     *
     * @param repositoryId The repository
     * @param key          The key
     */

    record Parameters(
      NPRepositoryID repositoryId,
      NPFingerprint key)
    {
      /**
       * The parameters.
       */

      public Parameters
      {
        Objects.requireNonNull(repositoryId, "repositoryId");
        Objects.requireNonNull(key, "key");
      }
    }
  }

  /**
   * Check if a key is assigned to a repository.
   */

  non-sealed interface RepositoryPublicKeyIsAssignedType
    extends NPDatabaseQueryType<RepositoryPublicKeyIsAssignedType.Parameters, Boolean>,
    NPDatabaseQueriesRepositoriesType
  {
    /**
     * The parameters.
     *
     * @param repositoryId The repository
     * @param key          The key
     */

    record Parameters(
      NPRepositoryID repositoryId,
      NPFingerprint key)
    {
      /**
       * The parameters.
       */

      public Parameters
      {
        Objects.requireNonNull(repositoryId, "repositoryId");
        Objects.requireNonNull(key, "key");
      }
    }
  }

  /**
   * Retrieve the set of keys assigned to a repository.
   */

  non-sealed interface RepositoryPublicKeysAssignedType
    extends NPDatabaseQueryType<NPRepositoryID, Set<NPFingerprint>>,
    NPDatabaseQueriesRepositoriesType
  {

  }
}
