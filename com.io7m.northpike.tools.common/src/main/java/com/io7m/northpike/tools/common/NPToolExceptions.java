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

import com.io7m.jdownload.core.JDownloadErrorChecksumMismatch;
import com.io7m.jdownload.core.JDownloadErrorHTTP;
import com.io7m.jdownload.core.JDownloadErrorIO;
import com.io7m.jdownload.core.JDownloadErrorType;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.strings.NPStringConstants;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.tools.api.NPToolException;

import java.io.IOException;
import java.net.URISyntaxException;
import java.nio.file.Path;
import java.util.Map;
import java.util.Optional;

import static com.io7m.northpike.strings.NPStringConstants.ENTRY;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_HASH_MISMATCH;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_HTTP;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_IO;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_PARSE;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_UNSAFE_ARCHIVE_PATH;
import static com.io7m.northpike.strings.NPStringConstants.FILE;
import static com.io7m.northpike.strings.NPStringConstants.HASH_ALGO;
import static com.io7m.northpike.strings.NPStringConstants.HASH_EXPECTED;
import static com.io7m.northpike.strings.NPStringConstants.HASH_RECEIVED;
import static com.io7m.northpike.strings.NPStringConstants.HTTP_STATUS;

/**
 * Functions to produce {@link NPToolException} values.
 */

public final class NPToolExceptions
{
  private NPToolExceptions()
  {

  }

  /**
   * Produce an exception from an I/O error.
   *
   * @param strings The string resources
   * @param e       The exception
   *
   * @return The resulting exception
   */

  public static NPToolException errorIO(
    final NPStrings strings,
    final IOException e)
  {
    return new NPToolException(
      strings.format(ERROR_IO),
      e,
      NPStandardErrorCodes.errorIo(),
      Map.of(),
      Optional.empty()
    );
  }

  /**
   * Produce an exception from a malformed URI error.
   *
   * @param strings   The string resources
   * @param e         The exception
   * @param targetURI The URI
   *
   * @return The resulting exception
   */

  public static NPToolException errorURI(
    final NPStrings strings,
    final String targetURI,
    final URISyntaxException e)
  {
    return new NPToolException(
      strings.format(ERROR_PARSE),
      e,
      NPStandardErrorCodes.errorParse(),
      Map.ofEntries(
        Map.entry(
          strings.format(NPStringConstants.URI),
          targetURI
        )
      ),
      Optional.empty()
    );
  }

  /**
   * Produce an exception from an HTTP status error.
   *
   * @param strings   The string resources
   * @param targetURI The URI
   * @param status    The HTTP status code
   *
   * @return The resulting exception
   */

  public static NPToolException errorHttp(
    final NPStrings strings,
    final String targetURI,
    final int status)
  {
    return new NPToolException(
      strings.format(ERROR_HTTP),
      NPStandardErrorCodes.errorIo(),
      Map.ofEntries(
        Map.entry(
          strings.format(HTTP_STATUS),
          Integer.toString(status)
        ),
        Map.entry(
          strings.format(NPStringConstants.URI),
          targetURI
        )
      ),
      Optional.empty()
    );
  }

  /**
   * Produce an exception from a checksum mismatch error.
   *
   * @param strings      The string resources
   * @param file         The file
   * @param algorithm    The algorithm
   * @param expectedHash The expected hash value
   * @param receivedHash The received hash value
   *
   * @return The resulting exception
   */

  public static NPToolException errorChecksumMismatch(
    final NPStrings strings,
    final Path file,
    final String algorithm,
    final String expectedHash,
    final String receivedHash)
  {
    return new NPToolException(
      strings.format(ERROR_HASH_MISMATCH),
      NPStandardErrorCodes.errorIo(),
      Map.ofEntries(
        Map.entry(
          strings.format(HASH_ALGO),
          algorithm
        ),
        Map.entry(
          strings.format(HASH_EXPECTED),
          expectedHash
        ),
        Map.entry(
          strings.format(HASH_RECEIVED),
          receivedHash
        ),
        Map.entry(
          strings.format(FILE),
          file.toAbsolutePath().toString()
        )
      ),
      Optional.empty()
    );
  }

  /**
   * Produce an exception from an unsafe archive entry element.
   *
   * @param strings The string resources
   * @param file    The file
   * @param entry   The entry
   *
   * @return The resulting exception
   */

  public static NPToolException errorUnsafeArchivePath(
    final NPStrings strings,
    final Path file,
    final String entry)
  {
    return new NPToolException(
      strings.format(ERROR_UNSAFE_ARCHIVE_PATH),
      NPStandardErrorCodes.errorUnsafeArchiveEntry(),
      Map.ofEntries(
        Map.entry(
          strings.format(FILE),
          file.toString()
        ),
        Map.entry(
          strings.format(ENTRY),
          entry
        )
      ),
      Optional.empty()
    );
  }

  /**
   * Produce an exception from a download error.
   *
   * @param strings The string resources
   * @param error   The error
   *
   * @return The resulting exception
   */

  public static NPToolException errorOfDownloadError(
    final NPStrings strings,
    final JDownloadErrorType error)
  {
    return switch (error) {
      case final JDownloadErrorIO io -> {
        yield errorIO(strings, io.exception());
      }
      case final JDownloadErrorChecksumMismatch mismatch -> {
        yield errorChecksumMismatch(
          strings,
          mismatch.outputFile(),
          mismatch.algorithm(),
          mismatch.hashExpected(),
          mismatch.hashReceived()
        );
      }
      case final JDownloadErrorHTTP http -> {
        yield errorHttp(strings, http.uri().toString(), http.status());
      }
    };
  }
}
