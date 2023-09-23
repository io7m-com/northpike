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


package com.io7m.northpike.tests.keys;

import com.io7m.northpike.keys.NPPublicKeys;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPFingerprint;
import com.io7m.northpike.model.NPPublicKey;
import org.junit.jupiter.api.Test;

import java.io.InputStream;
import java.time.OffsetDateTime;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import static java.nio.charset.StandardCharsets.UTF_8;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

public final class NPPublicKeysTest
{
  private static final String KEY_TEXT = """
    -----BEGIN PGP PUBLIC KEY BLOCK-----
    Version: BCPG v1.76.0

    mDMEY7F/wRYJKwYBBAHaRw8BAQdA5iaeazlPKvs/ThTquJ4lYrjTwI9ALsyTu3/V
    mWUYSfm0Lk1hcmsgUmF5bnNmb3JkICgyMDIzIHBlcnNvbmFsKSA8bWFya0Bpbzdt
    LmNvbT6IlgQTFggAPhYhBKQ4pzfHcXhxlc/BZvhDUfcskYR2BQJjsYAuAhsDBQkB
    4SmgBQsJCAcDBRUKCQgLBRYCAwEAAh4BAheAAAoJEPhDUfcskYR2sZUBAJ02ki3d
    GSe+MjjDKXLOaS+8amInjuASuPF2LPbfDMWhAP9VxsqMpyIiseO0o0TeJze8PT58
    33+QQL5aV5ZSUOAuB7Q+TWFyayBSYXluc2ZvcmQgKDIwMjMgcGVyc29uYWwgW0dp
    dEh1YiBzdWJ1aWRdKSA8Y29kZUBpbzdtLmNvbT6IlgQTFggAPhYhBKQ4pzfHcXhx
    lc/BZvhDUfcskYR2BQJjsX//AhsDBQkB4SmgBQsJCAcDBRUKCQgLBRYCAwEAAh4B
    AheAAAoJEPhDUfcskYR2lGIBAJ8Nwbhntp+YhLYJM0j3jFDt7+S3QgnyAsIiUaHa
    /wrmAQDv1ZAVG5D1D6UYlgDSHBFzoijRXb3XBvwTRogQM/zJCw==
    =Ri3k
    -----END PGP PUBLIC KEY BLOCK-----
    """;

  @Test
  public void testDecodeSecret()
    throws Exception
  {
    final var ex =
      assertThrows(NPException.class, () -> {
        NPPublicKeys.decode(resource("key-sec-0.asc"));
      });

    assertTrue(ex.getMessage().contains("PGPSecretKeyRing"));
  }

  @Test
  public void testDecodeFile()
    throws Exception
  {
    final var keys =
      NPPublicKeys.decode(resource("key-pub-0.asc"));

    checkKeys(keys);
  }

  @Test
  public void testDecodeString()
    throws Exception
  {
    final var text =
      new String(resource("key-pub-0.asc").readAllBytes(), UTF_8);

    final var keys =
      NPPublicKeys.decodeString(text);

    checkKeys(keys);
  }

  private static void checkKeys(final List<NPPublicKey> keys)
  {
    assertEquals(1, keys.size());

    final var k = keys.get(0);
    assertTrue(
      k.userIDs().contains("Mark Raynsford (2023 personal) <mark@io7m.com>")
    );
    assertTrue(
      k.userIDs().contains(
        "Mark Raynsford (2023 personal [GitHub subuid]) <code@io7m.com>")
    );
    assertEquals(
      new NPFingerprint("a438a737c771787195cfc166f84351f72c918476"),
      k.fingerprint()
    );
    assertEquals(
      OffsetDateTime.parse("2023-01-01T12:42:41Z"),
      k.timeCreated()
    );
    assertEquals(
      Optional.of(OffsetDateTime.parse("2024-01-01T12:00:33Z")),
      k.timeExpires()
    );

    assertEquals(
      KEY_TEXT.lines()
        .map(String::trim)
        .collect(Collectors.joining("\r\n")),
      k.encodedForm()
    );
  }

  private static InputStream resource(
    final String name)
  {
    return NPPublicKeysTest.class
      .getResourceAsStream("/com/io7m/northpike/tests/" + name);
  }
}
