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


package com.io7m.northpike.server.internal.repositories;

import com.io7m.jmulticlose.core.CloseableType;
import com.io7m.northpike.keys.NPSignatureKeyLookupType;
import com.io7m.northpike.model.NPArchive;
import com.io7m.northpike.model.NPAuditOwnerType;
import com.io7m.northpike.model.NPCommit;
import com.io7m.northpike.model.NPCommitID;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPFingerprint;
import com.io7m.northpike.model.NPRepositoryDescription;
import com.io7m.northpike.model.NPRepositoryID;
import com.io7m.northpike.model.NPRepositorySigningPolicy;
import com.io7m.repetoir.core.RPServiceType;

import java.util.Optional;
import java.util.concurrent.CompletableFuture;

/**
 * The repository service.
 */

public interface NPRepositoryServiceType
  extends CloseableType, RPServiceType
{
  /**
   * Start the service running.
   *
   * @param startup The startup behaviour
   *
   * @return A future representing the service startup
   */

  CompletableFuture<Void> start(
    NPRepositoryStartup startup);

  /**
   * Update all repositories.
   *
   * @return A future representing the operation in progress
   */

  CompletableFuture<Void> update();

  /**
   * Check/update the given repository.
   *
   * @param id The repository ID
   *
   * @return A future representing the operation in progress
   */

  CompletableFuture<Void> repositoryUpdate(
    NPRepositoryID id);

  /**
   * Create an archive for the given commit.
   *
   * @param commit The commit
   *
   * @return The archive
   *
   * @throws InterruptedException On interruption
   * @throws NPException          On errors
   */

  NPArchive commitCreateArchiveFor(
    NPCommitID commit)
    throws InterruptedException, NPException;

  /**
   * Verify the signature for the given commit.
   *
   * @param commit    The commit
   * @param keyLookup The key lookup
   *
   * @return The verified signature
   *
   * @throws InterruptedException On interruption
   * @throws NPException          On errors
   */

  NPFingerprint commitSignatureVerify(
    NPCommitID commit,
    NPSignatureKeyLookupType keyLookup)
    throws InterruptedException, NPException;

  /**
   * Determine if the given public key is assigned to the given repository.
   *
   * @param repository  The repository
   * @param fingerprint The public key
   *
   * @return {@code true} if the key is assigned to the repository
   *
   * @throws InterruptedException On interruption
   * @throws NPException          On errors
   */

  boolean repositoryHasPublicKeyAssigned(
    NPRepositoryID repository,
    NPFingerprint fingerprint)
    throws InterruptedException, NPException;

  /**
   * Get the signing policy for the given repository.
   *
   * @param repository The repository
   *
   * @return The signing policy
   *
   * @throws InterruptedException On interruption
   * @throws NPException          On errors
   */

  NPRepositorySigningPolicy repositorySigningPolicyFor(
    NPRepositoryID repository)
    throws InterruptedException, NPException;

  /**
   * Get the commit with the given ID.
   *
   * @param commitID The commit ID
   *
   * @return The commit
   *
   * @throws InterruptedException On interruption
   * @throws NPException          On errors and nonexistent commits
   */

  NPCommit commitGet(
    NPCommitID commitID)
    throws InterruptedException, NPException;

  /**
   * Retrieve a repository.
   *
   * @param repository The repository ID
   *
   * @return A repository description
   *
   * @throws NPException On errors
   */

  Optional<NPRepositoryDescription> repositoryGet(
    NPRepositoryID repository)
    throws NPException;

  /**
   * Create or update a repository.
   *
   * @param owner      The owner of the update
   * @param repository The repository
   *
   * @throws NPException On errors
   */

  void repositoryPut(
    NPAuditOwnerType owner,
    NPRepositoryDescription repository)
    throws NPException;

  /**
   * Assign a public key to a repository.
   *
   * @param owner      The owner of the update
   * @param repository The repository
   * @param key        The key
   *
   * @throws NPException On errors
   */

  void repositoryPublicKeyAssign(
    NPAuditOwnerType owner,
    NPRepositoryID repository,
    NPFingerprint key)
    throws NPException;
}
