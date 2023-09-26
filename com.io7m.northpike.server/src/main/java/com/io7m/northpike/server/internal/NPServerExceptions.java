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


package com.io7m.northpike.server.internal;

import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPRepositoryID;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.server.api.NPServerException;
import com.io7m.northpike.strings.NPStringConstants;
import com.io7m.northpike.strings.NPStrings;

import java.io.IOException;
import java.net.URI;
import java.security.GeneralSecurityException;
import java.util.Map;
import java.util.Optional;

import static com.io7m.northpike.strings.NPStringConstants.ERROR_IO;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_REPOSITORY_UNSUPPORTED_PROVIDER;
import static com.io7m.northpike.strings.NPStringConstants.REPOSITORY;

/**
 * Functions to create server exceptions.
 */

public final class NPServerExceptions
{
  private NPServerExceptions()
  {

  }

  /**
   * An I/O exception occurred.
   *
   * @param strings The string resources
   * @param e       The underlying I/O exception
   *
   * @return An exception
   */

  public static NPServerException errorIO(
    final NPStrings strings,
    final IOException e)
  {
    return new NPServerException(
      strings.format(ERROR_IO),
      e,
      NPStandardErrorCodes.errorIo(),
      Map.of(),
      Optional.empty()
    );
  }

  /**
   * An unsupported SCM repository configuration was encountered.
   *
   * @param strings  The string resources
   * @param uri      The URI
   * @param id       The repository ID
   * @param provider The repository provider
   *
   * @return An exception
   */

  public static NPServerException errorUnsupportedSCMProvider(
    final NPStrings strings,
    final NPRepositoryID id,
    final URI uri,
    final RDottedName provider)
  {
    return new NPServerException(
      strings.format(ERROR_REPOSITORY_UNSUPPORTED_PROVIDER),
      NPStandardErrorCodes.errorUnsupported(),
      Map.ofEntries(
        Map.entry(
          strings.format(REPOSITORY),
          id.toString()
        ),
        Map.entry(
          strings.format(NPStringConstants.URI),
          uri.toString()
        ),
        Map.entry(
          strings.format(NPStringConstants.SCM_PROVIDER),
          provider.toString()
        )
      ),
      Optional.empty()
    );
  }

  /**
   * Wrap the given exception as a server exception.
   *
   * @param e The exception
   *
   * @return A server exception
   */

  public static NPServerException wrap(
    final NPException e)
  {
    if (e instanceof final NPServerException es) {
      return es;
    }

    return new NPServerException(
      e.getMessage(),
      e,
      e.errorCode(),
      e.attributes(),
      e.remediatingAction()
    );
  }

  /**
   * Wrap the given exception as a server exception.
   *
   * @param e The exception
   *
   * @return A server exception
   */

  public static NPServerException errorSecurity(
    final GeneralSecurityException e)
  {
    return new NPServerException(
      e.getMessage(),
      e,
      NPStandardErrorCodes.errorIo(),
      Map.of(),
      Optional.empty()
    );
  }
}
