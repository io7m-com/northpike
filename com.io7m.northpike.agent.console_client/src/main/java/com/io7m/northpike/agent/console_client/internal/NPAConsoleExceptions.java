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


package com.io7m.northpike.agent.console_client.internal;

import com.io7m.northpike.agent.console_client.api.NPAConsoleClientException;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.strings.NPStrings;

import java.io.IOException;
import java.security.GeneralSecurityException;
import java.util.Map;
import java.util.Optional;

import static com.io7m.northpike.strings.NPStringConstants.ERROR_IO;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_PROTOCOL;
import static com.io7m.northpike.strings.NPStringConstants.EXPECTED;
import static com.io7m.northpike.strings.NPStringConstants.RECEIVED;


/**
 * Functions to handle agent exceptions.
 */

final class NPAConsoleExceptions
{
  private NPAConsoleExceptions()
  {

  }

  static NPAConsoleClientException errorIO(
    final NPStrings strings,
    final IOException e)
  {
    return new NPAConsoleClientException(
      strings.format(ERROR_IO),
      e,
      NPStandardErrorCodes.errorIo(),
      Map.of(),
      Optional.empty()
    );
  }

  static NPAConsoleClientException errorProtocol(
    final NPProtocolException e)
  {
    return new NPAConsoleClientException(
      e.getMessage(),
      e,
      e.errorCode(),
      e.attributes(),
      e.remediatingAction()
    );
  }

  static NPAConsoleClientException errorUnexpectedMessage(
    final NPStrings strings,
    final Class<?> expected,
    final Object received)
  {
    return new NPAConsoleClientException(
      strings.format(ERROR_PROTOCOL),
      NPStandardErrorCodes.errorProtocol(),
      Map.ofEntries(
        Map.entry(
          strings.format(EXPECTED),
          expected.getSimpleName()
        ),
        Map.entry(
          strings.format(RECEIVED),
          received.getClass().getSimpleName()
        )
      ),
      Optional.empty()
    );
  }

  public static NPAConsoleClientException errorSecurity(
    final GeneralSecurityException e)
  {
    return new NPAConsoleClientException(
      e.getMessage(),
      e,
      NPStandardErrorCodes.errorIo(),
      Map.of(),
      Optional.empty()
    );
  }

  public static NPAConsoleClientException wrap(
    final NPException e)
  {
    return new NPAConsoleClientException(
      e.getMessage(),
      e,
      e.errorCode(),
      e.attributes(),
      e.remediatingAction()
    );
  }
}
