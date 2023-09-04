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


package com.io7m.northpike.protocol.user;

import com.io7m.idstore.model.IdName;

import java.util.Objects;
import java.util.UUID;

/**
 * Log in.
 *
 * @param messageID The ID of this message
 * @param name      The username
 * @param password  The password
 */

public record NPUCommandLogin(
  UUID messageID,
  IdName name,
  String password)
  implements NPUCommandType<NPUResponseOK>
{
  /**
   * Log in.
   *
   * @param messageID The ID of this message
   * @param name      The username
   * @param password  The password
   */

  public NPUCommandLogin
  {
    Objects.requireNonNull(messageID, "messageID");
    Objects.requireNonNull(name, "key");
  }

  /**
   * Create a login command.
   *
   * @param name     The name
   * @param password The password
   *
   * @return A login command
   */

  public static NPUCommandLogin of(
    final String name,
    final String password)
  {
    return of(new IdName(name), password);
  }

  /**
   * Create a login command.
   *
   * @param name     The name
   * @param password The password
   *
   * @return A login command
   */

  public static NPUCommandLogin of(
    final IdName name,
    final String password)
  {
    return new NPUCommandLogin(
      UUID.randomUUID(),
      name,
      password
    );
  }

  @Override
  public Class<NPUResponseOK> responseClass()
  {
    return NPUResponseOK.class;
  }
}
