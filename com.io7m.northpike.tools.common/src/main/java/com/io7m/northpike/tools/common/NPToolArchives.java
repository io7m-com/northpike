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


package com.io7m.northpike.tools.common;

import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.tools.api.NPToolException;
import org.apache.commons.compress.archivers.tar.TarArchiveEntry;
import org.apache.commons.compress.archivers.tar.TarArchiveInputStream;

import java.io.BufferedInputStream;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.attribute.PosixFilePermissions;
import java.security.NoSuchAlgorithmException;
import java.security.SecureRandom;
import java.util.HexFormat;
import java.util.Objects;
import java.util.zip.GZIPInputStream;

import static com.io7m.northpike.tools.common.NPToolResources.createResourceCollection;
import static java.nio.file.StandardCopyOption.ATOMIC_MOVE;
import static java.nio.file.StandardCopyOption.REPLACE_EXISTING;
import static java.nio.file.StandardOpenOption.CREATE;
import static java.nio.file.StandardOpenOption.TRUNCATE_EXISTING;

/**
 * Convenience functions to unpack archives.
 */

public final class NPToolArchives
{
  private final NPStrings strings;
  private final SecureRandom rng;

  /**
   * Convenience functions to unpack archives.
   *
   * @param inStrings The string resources
   */

  public NPToolArchives(
    final NPStrings inStrings)
  {
    this.strings =
      Objects.requireNonNull(inStrings, "strings");

    try {
      this.rng = SecureRandom.getInstanceStrong();
    } catch (final NoSuchAlgorithmException e) {
      throw new IllegalStateException(e);
    }
  }

  /**
   * Unpack the archive {@code file} into {@code outputDirectory}.
   *
   * @param file            The archive file
   * @param outputDirectory The output directory
   *
   * @throws NPToolException On errors
   */

  public void unpackTarGZ(
    final Path file,
    final Path outputDirectory)
    throws NPToolException
  {
    Objects.requireNonNull(file, "file");
    Objects.requireNonNull(outputDirectory, "outputDirectory");

    try (var resources = createResourceCollection(this.strings)) {
      final var input =
        resources.add(Files.newInputStream(file));
      final var buffered =
        resources.add(new BufferedInputStream(input));
      final var gzip =
        resources.add(new GZIPInputStream(buffered));
      final var tar =
        resources.add(new TarArchiveInputStream(gzip));

      while (true) {
        final var entry = tar.getNextTarEntry();
        if (entry == null) {
          break;
        }

        final var path =
          outputDirectory.resolve(entry.getName())
            .toAbsolutePath()
            .normalize();

        if (!path.startsWith(outputDirectory)) {
          throw NPToolExceptions.errorUnsafeArchivePath(
            this.strings,
            file,
            entry.getName()
          );
        }

        if (entry.isDirectory()) {
          createDirectory(entry, path);
        } else if (entry.isFile()) {
          this.createFileFromStream(tar, entry, path);
        }
      }
    } catch (final IOException e) {
      throw NPToolExceptions.errorIO(this.strings, e);
    }
  }

  private void createFileFromStream(
    final TarArchiveInputStream tar,
    final TarArchiveEntry entry,
    final Path path)
    throws IOException
  {
    final var token = new byte[8];
    this.rng.nextBytes(token);
    final var tokenText =
      HexFormat.of().formatHex(token);

    final var pathTemp =
      path.resolveSibling("%s.%s".formatted(path.getFileName(), tokenText));
    final var parent =
      pathTemp.getParent();

    if (parent != null) {
      Files.createDirectories(parent);
    }

    try (var output =
           Files.newOutputStream(pathTemp, TRUNCATE_EXISTING, CREATE)) {
      output.write(tar.readAllBytes());
      output.flush();

      Files.move(pathTemp, path, REPLACE_EXISTING, ATOMIC_MOVE);

      try {
        Files.setPosixFilePermissions(
          path,
          PosixFilePermissions.fromString(permissionString(entry.getMode()))
        );
      } catch (final UnsupportedOperationException e) {
        // Not a POSIX filesystem.
      }
    }
  }

  private static String permissionString(
    final int mode)
  {
    final var bits = new char[9];
    permissionStringOwner(mode, bits);
    permissionStringGroup(mode, bits);
    permissionStringWorld(mode, bits);
    return new String(bits);
  }

  private static void permissionStringWorld(
    final int mode,
    final char[] bits)
  {
    bits[6] = ((mode & 0b000_000_100) == 0b000_000_100) ? 'r' : '-';
    bits[7] = ((mode & 0b000_000_010) == 0b000_000_010) ? 'w' : '-';
    bits[8] = ((mode & 0b000_000_001) == 0b000_000_001) ? 'x' : '-';
  }

  private static void permissionStringGroup(
    final int mode,
    final char[] bits)
  {
    bits[3] = ((mode & 0b000_100_000) == 0b000_100_000) ? 'r' : '-';
    bits[4] = ((mode & 0b000_010_000) == 0b000_010_000) ? 'w' : '-';
    bits[5] = ((mode & 0b000_001_000) == 0b000_001_000) ? 'x' : '-';
  }

  private static void permissionStringOwner(
    final int mode,
    final char[] bits)
  {
    bits[0] = ((mode & 0b100_000_000) == 0b100_000_000) ? 'r' : '-';
    bits[1] = ((mode & 0b010_000_000) == 0b010_000_000) ? 'w' : '-';
    bits[2] = ((mode & 0b001_000_000) == 0b001_000_000) ? 'x' : '-';
  }

  private static void createDirectory(
    final TarArchiveEntry entry,
    final Path path)
    throws IOException
  {
    Files.createDirectories(path);
  }
}
