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

package com.io7m.northpike.server.internal.idstore;

import com.io7m.idstore.user_client.api.IdUClientException;
import com.io7m.idstore.user_client.api.IdUClientSynchronousType;
import com.io7m.repetoir.core.RPServiceType;

import java.net.URI;

/**
 * Idstore clients.
 */

public interface NPIdstoreClientsType extends RPServiceType
{
  /**
   * Create a new client.
   *
   * @return A new client
   *
   * @throws IdUClientException   On client errors
   * @throws InterruptedException On interruption
   */

  IdUClientSynchronousType createClient()
    throws IdUClientException, InterruptedException;

  /**
   * @return The base URI of the idstore server
   */

  URI baseURI();

  /**
   * @return The password reset URI for the idstore server
   */

  URI passwordResetURI();
}
