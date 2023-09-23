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


package com.io7m.northpike.keys;

import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPFingerprint;
import com.io7m.northpike.model.NPPublicKey;
import com.io7m.northpike.model.NPStandardErrorCodes;
import org.bouncycastle.bcpg.ArmoredOutputStream;
import org.bouncycastle.openpgp.PGPException;
import org.bouncycastle.openpgp.PGPUtil;
import org.bouncycastle.openpgp.jcajce.JcaPGPPublicKeyRingCollection;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.OffsetDateTime;
import java.time.ZoneId;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.HexFormat;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import static java.nio.charset.StandardCharsets.UTF_8;

/**
 * Functions to load public keys.
 */

public final class NPPublicKeys
{
  private static final HexFormat HEX = HexFormat.of();

  private NPPublicKeys()
  {

  }

  /**
   * Decode a public key from the given text.
   *
   * @param text The ASCII-armored key
   *
   * @return A public key
   *
   * @throws NPException On errors
   */

  public static List<NPPublicKey> decodeString(
    final String text)
    throws NPException
  {
    try (var stream = new ByteArrayInputStream(text.getBytes(UTF_8))) {
      return decode(stream);
    } catch (final IOException e) {
      throw new NPException(
        e.getMessage(),
        e,
        NPStandardErrorCodes.errorIo(),
        Map.of(),
        Optional.empty()
      );
    }
  }

  /**
   * Decode a public key from the given file.
   *
   * @param file The file
   *
   * @return A public key
   *
   * @throws NPException On errors
   */

  public static List<NPPublicKey> decodeFile(
    final Path file)
    throws NPException
  {
    try (var stream = Files.newInputStream(file)) {
      return decode(stream);
    } catch (final IOException e) {
      throw new NPException(
        e.getMessage(),
        e,
        NPStandardErrorCodes.errorIo(),
        Map.of(),
        Optional.empty()
      );
    }
  }

  /**
   * Decode a public key from the given stream.
   *
   * @param stream The stream
   *
   * @return A public key
   *
   * @throws NPException On errors
   */

  public static List<NPPublicKey> decode(
    final InputStream stream)
    throws NPException
  {
    final var results =
      new ArrayList<NPPublicKey>();

    try (var decoder = PGPUtil.getDecoderStream(stream)) {
      final var keyRingCollection =
        new JcaPGPPublicKeyRingCollection(decoder);
      final var keyRings =
        keyRingCollection.getKeyRings();

      while (keyRings.hasNext()) {
        final var keyRing =
          keyRings.next();
        final var keys =
          keyRing.getPublicKeys();

        while (keys.hasNext()) {
          final var key = keys.next();

          final var timeCreated =
            OffsetDateTime.ofInstant(
              key.getCreationTime().toInstant(),
              ZoneId.of("UTC")
            );

          final Optional<OffsetDateTime> timeExpires;
          if (key.getValidSeconds() != 0L) {
            timeExpires = Optional.of(
              timeCreated.plusSeconds(key.getValidSeconds())
            );
          } else {
            timeExpires = Optional.empty();
          }

          final var userIDs = userIds(key.getUserIDs());
          if (userIDs.isEmpty()) {
            continue;
          }

          results.add(
            new NPPublicKey(
              userIDs,
              new NPFingerprint(HEX.formatHex(key.getFingerprint())),
              timeCreated,
              timeExpires,
              armor(key.getEncoded(true))
            )
          );
        }
      }

      return List.copyOf(results);
    } catch (final IOException | PGPException e) {
      throw new NPException(
        e.getMessage(),
        e,
        NPStandardErrorCodes.errorIo(),
        Map.of(),
        Optional.empty()
      );
    }
  }

  private static Set<String> userIds(
    final Iterator<String> userIDs)
  {
    final var results = new HashSet<String>();
    while (userIDs.hasNext()) {
      results.add(userIDs.next());
    }
    return Set.copyOf(results);
  }

  private static String armor(
    final byte[] encoded)
    throws IOException
  {
    try (var outBytes = new ByteArrayOutputStream()) {
      try (var output = new ArmoredOutputStream(outBytes)) {
        output.write(encoded);
        output.flush();
      }
      return outBytes.toString(UTF_8)
        .lines()
        .map(String::trim)
        .collect(Collectors.joining("\r\n"));
    }
  }
}
