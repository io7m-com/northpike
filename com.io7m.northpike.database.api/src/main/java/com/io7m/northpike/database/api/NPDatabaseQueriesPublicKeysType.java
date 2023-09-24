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


import com.io7m.northpike.model.NPFingerprint;
import com.io7m.northpike.model.NPPublicKey;
import com.io7m.northpike.model.NPPublicKeySearchParameters;

import java.util.Optional;

/**
 * The database queries involving public keys.
 */

public sealed interface NPDatabaseQueriesPublicKeysType
  extends NPDatabaseQueriesType
{
  /**
   * Update the given public key.
   */

  non-sealed interface PutType
    extends NPDatabaseQueryType<NPPublicKey, NPDatabaseUnit>,
    NPDatabaseQueriesPublicKeysType
  {

  }

  /**
   * Retrieve a public key.
   */

  non-sealed interface GetType
    extends NPDatabaseQueryType<NPFingerprint, Optional<NPPublicKey>>,
    NPDatabaseQueriesPublicKeysType
  {

  }

  /**
   * Search public keys.
   */

  non-sealed interface SearchType
    extends NPDatabaseQueryType<NPPublicKeySearchParameters, NPPublicKeysPagedType>,
    NPDatabaseQueriesPublicKeysType
  {

  }

  /**
   * Delete the given public key.
   */

  non-sealed interface DeleteType
    extends NPDatabaseQueryType<NPFingerprint, NPDatabaseUnit>,
    NPDatabaseQueriesPublicKeysType
  {

  }
}
