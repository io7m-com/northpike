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


package com.io7m.northpike.model;

import java.time.OffsetDateTime;
import java.util.Objects;

/**
 * A reference to an archive.
 *
 * @param token   The unique archive token
 * @param commit  The commit that produced the archive
 * @param hash    The hash of the archive data
 * @param created The time the archive was created
 */

public record NPArchive(
  NPToken token,
  NPCommitID commit,
  NPHash hash,
  OffsetDateTime created)
{
  /**
   * A reference to an archive.
   *
   * @param token   The unique archive token
   * @param commit  The commit that produced the archive
   * @param hash    The hash of the archive data
   * @param created The time the archive was created
   */

  public NPArchive
  {
    Objects.requireNonNull(token, "token");
    Objects.requireNonNull(commit, "commit");
    Objects.requireNonNull(hash, "hash");
    Objects.requireNonNull(created, "created");
  }

  /**
   * @param token The token
   *
   * @return The filename an archive with the given token would have
   */

  public static String fileNameFor(
    final NPToken token)
  {
    return "%s.tgz".formatted(token.value());
  }

  /**
   * @param token The token
   *
   * @return The filename a checksum file for the archive with the given
   * token would have
   */

  public static String checksumFileNameFor(
    final NPToken token)
  {
    return "%s.tgz.sha256".formatted(token.value());
  }

  /**
   * @param token The token
   *
   * @return The filename a temporary checksum file for the archive with the
   * given token would have
   */

  public static String checksumFileNameForTemporary(
    final NPToken token)
  {
    return "%s.tgz.sha256.tmp".formatted(token.value());
  }

  /**
   * @param token The token
   *
   * @return The filename a temporary archive with the given token would have
   */

  public static String fileNameForTemporary(
    final NPToken token)
  {
    return "%s.tgz.tmp".formatted(token.value());
  }

  /**
   * @return The filename for this archive
   */

  public String fileName()
  {
    return fileNameFor(this.token);
  }

  /**
   * @return The filename for the checksum of this archive
   */

  public String checksumFileName()
  {
    return checksumFileNameFor(this.token);
  }
}
