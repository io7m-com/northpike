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

import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;

/**
 * The database queries involving repositories.
 */

public sealed interface NPDatabaseQueriesRepositoriesType
  extends NPDatabaseQueriesType
{
  /**
   * Update the given repository.
   */

  non-sealed interface PutType
    extends NPDatabaseQueryType<NPRepositoryDescription, NPDatabaseUnit>,
    NPDatabaseQueriesRepositoriesType
  {

  }

  /**
   * Retrieve a repository.
   */

  non-sealed interface GetType
    extends NPDatabaseQueryType<UUID, Optional<NPRepositoryDescription>>,
    NPDatabaseQueriesRepositoriesType
  {

  }

  /**
   * List repositories.
   */

  non-sealed interface ListType
    extends NPDatabaseQueryType<NPDatabaseUnit, NPRepositoriesPagedType>,
    NPDatabaseQueriesRepositoriesType
  {

  }

  /**
   * Add or update commits in the given repository.
   */

  non-sealed interface CommitsPutType
    extends NPDatabaseQueryType<CommitsPutType.Parameters, NPDatabaseUnit>,
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

  non-sealed interface CommitGetType
    extends NPDatabaseQueryType<NPCommitID, Optional<NPCommit>>,
    NPDatabaseQueriesRepositoriesType
  {

  }

  /**
   * List commits in the repository.
   */

  non-sealed interface CommitsGetType
    extends NPDatabaseQueryType<NPCommitSearchParameters, NPCommitSummaryLinkedPagedType>,
    NPDatabaseQueriesRepositoriesType
  {

  }

  /**
   * Get the most recently received commit in the repository.
   */

  non-sealed interface CommitsGetMostRecentlyReceivedType
    extends NPDatabaseQueryType<UUID, Optional<NPCommitSummary>>,
    NPDatabaseQueriesRepositoriesType
  {

  }

  /**
   * Assign a key to a repository.
   */

  non-sealed interface PublicKeyAssignType
    extends NPDatabaseQueryType<PublicKeyAssignType.Parameters, NPDatabaseUnit>,
    NPDatabaseQueriesRepositoriesType
  {
    /**
     * The parameters.
     *
     * @param repositoryId The repository
     * @param key          The key
     */

    record Parameters(
      UUID repositoryId,
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

  non-sealed interface PublicKeyUnassignType
    extends NPDatabaseQueryType<PublicKeyUnassignType.Parameters, NPDatabaseUnit>,
    NPDatabaseQueriesRepositoriesType
  {
    /**
     * The parameters.
     *
     * @param repositoryId The repository
     * @param key          The key
     */

    record Parameters(
      UUID repositoryId,
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

  non-sealed interface PublicKeyIsAssignedType
    extends NPDatabaseQueryType<PublicKeyIsAssignedType.Parameters, Boolean>,
    NPDatabaseQueriesRepositoriesType
  {
    /**
     * The parameters.
     *
     * @param repositoryId The repository
     * @param key          The key
     */

    record Parameters(
      UUID repositoryId,
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

  non-sealed interface PublicKeysAssignedType
    extends NPDatabaseQueryType<UUID, Set<NPFingerprint>>,
    NPDatabaseQueriesRepositoriesType
  {

  }
}
