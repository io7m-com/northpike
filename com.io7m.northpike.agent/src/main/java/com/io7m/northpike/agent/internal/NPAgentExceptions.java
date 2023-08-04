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


package com.io7m.northpike.agent.internal;

import com.io7m.northpike.agent.api.NPAgentException;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.strings.NPStrings;

import java.io.IOException;
import java.util.Map;
import java.util.Optional;

import static com.io7m.northpike.strings.NPStringConstants.ERROR_IO;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_PROTOCOL;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_READ_SHORT;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_SIZE_LIMIT_EXCEEDED;
import static com.io7m.northpike.strings.NPStringConstants.EXPECTED;
import static com.io7m.northpike.strings.NPStringConstants.LIMIT;
import static com.io7m.northpike.strings.NPStringConstants.RECEIVED;

/**
 * Functions to handle agent exceptions.
 */

final class NPAgentExceptions
{
  private NPAgentExceptions()
  {

  }

  static NPAgentException errorTooLarge(
    final NPStrings strings,
    final int messageSize,
    final int messageLimit)
  {
    return new NPAgentException(
      strings.format(ERROR_SIZE_LIMIT_EXCEEDED),
      NPStandardErrorCodes.errorIo(),
      Map.ofEntries(
        Map.entry(
          strings.format(LIMIT),
          Integer.toUnsignedString(messageLimit)
        ),
        Map.entry(
          strings.format(RECEIVED),
          Integer.toUnsignedString(messageSize)
        )
      ),
      Optional.empty()
    );
  }

  static NPAgentException errorShortRead(
    final NPStrings strings,
    final int expected,
    final int received)
  {
    return new NPAgentException(
      strings.format(ERROR_READ_SHORT),
      NPStandardErrorCodes.errorIo(),
      Map.ofEntries(
        Map.entry(
          strings.format(EXPECTED),
          Integer.toUnsignedString(expected)
        ),
        Map.entry(
          strings.format(RECEIVED),
          Integer.toUnsignedString(received)
        )
      ),
      Optional.empty()
    );
  }

  static NPAgentException errorIO(
    final NPStrings strings,
    final IOException e)
  {
    return new NPAgentException(
      strings.format(ERROR_IO),
      e,
      NPStandardErrorCodes.errorIo(),
      Map.of(),
      Optional.empty()
    );
  }

  static NPAgentException errorProtocol(
    final NPProtocolException e)
  {
    return new NPAgentException(
      e.getMessage(),
      e,
      e.errorCode(),
      e.attributes(),
      e.remediatingAction()
    );
  }

  static NPAgentException errorUnexpectedMessage(
    final NPStrings strings,
    final Class<?> expected,
    final Object received)
  {
    return new NPAgentException(
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
}
