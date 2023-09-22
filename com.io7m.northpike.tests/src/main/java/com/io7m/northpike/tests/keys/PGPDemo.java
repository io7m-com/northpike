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

import org.bouncycastle.bcpg.PublicKeyAlgorithmTags;
import org.bouncycastle.openpgp.PGPUtil;
import org.bouncycastle.openpgp.jcajce.JcaPGPPublicKeyRingCollection;

import java.nio.file.Files;
import java.nio.file.Paths;
import java.time.OffsetDateTime;
import java.time.ZoneId;
import java.util.HexFormat;

public final class PGPDemo
{
  private PGPDemo()
  {

  }

  private static String algorithmName(
    final int id)
  {
    return switch (id) {
      case PublicKeyAlgorithmTags.EDDSA_LEGACY -> "EDDSA_LEGACY";
      case PublicKeyAlgorithmTags.RSA_GENERAL -> "RSA_GENERAL";
      case PublicKeyAlgorithmTags.RSA_ENCRYPT -> "RSA_ENCRYPT";
      case PublicKeyAlgorithmTags.RSA_SIGN -> "RSA_SIGN";
      case PublicKeyAlgorithmTags.ELGAMAL_ENCRYPT -> "ELGAMAL_ENCRYPT";
      case PublicKeyAlgorithmTags.DSA -> "DSA";
      case PublicKeyAlgorithmTags.Ed448 -> "ED448";
      case PublicKeyAlgorithmTags.Ed25519 -> "ED25519";
      case PublicKeyAlgorithmTags.ECDH -> "ECDH";
      case PublicKeyAlgorithmTags.ECDSA -> "ECDSA";
      case PublicKeyAlgorithmTags.ELGAMAL_GENERAL -> "ELGAMAL_GENERAL";
      case PublicKeyAlgorithmTags.DIFFIE_HELLMAN -> "DIFFIE_HELLMAN";
      default -> "UNKNOWN(%d)".formatted(Integer.valueOf(id));
    };
  }

  public static void main(
    final String[] args)
    throws Exception
  {
    final var file = Paths.get(args[0]);

    try (var stream = Files.newInputStream(file)) {
      try (var decoder = PGPUtil.getDecoderStream(stream)) {
        final JcaPGPPublicKeyRingCollection keys =
          new JcaPGPPublicKeyRingCollection(decoder);

        keys.forEach(pubKeys -> {
          pubKeys.forEach(pubKey -> {
            final var hex = HexFormat.of();
            System.out.printf(
              "Fingerprint: %s%n",
              hex.formatHex(pubKey.getFingerprint())
            );

            System.out.printf(
              "Key Size: %d%n",
              pubKey.getBitStrength()
            );

            System.out.printf(
              "Key Algorithm: %s%n",
              algorithmName(pubKey.getAlgorithm())
            );

            final var ids = pubKey.getUserIDs();
            while (ids.hasNext()) {
              System.out.printf(
                "User ID: %s%n",
                ids.next()
              );
            }

            if (pubKey.getValidSeconds() != 0L) {
              final var timeNow =
                pubKey.getCreationTime().toInstant();
              final var timeThen =
                timeNow.plusSeconds(pubKey.getValidSeconds());

              System.out.printf(
                "Expires: %s%n",
                OffsetDateTime.ofInstant(timeThen, ZoneId.systemDefault())
              );
            } else {
              System.out.printf(
                "Expires: Never%n"
              );
            }
          });
        });
      }
    }
  }
}
