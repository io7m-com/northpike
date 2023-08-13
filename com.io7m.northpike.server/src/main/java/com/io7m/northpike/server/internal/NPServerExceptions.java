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

import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.server.api.NPServerException;
import com.io7m.northpike.strings.NPStrings;

import java.io.IOException;
import java.util.Map;
import java.util.Optional;

import static com.io7m.northpike.strings.NPStringConstants.ERROR_AUTHENTICATION;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_IO;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_PROTOCOL;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_READ_SHORT;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_SIZE_LIMIT_EXCEEDED;
import static com.io7m.northpike.strings.NPStringConstants.EXPECTED;
import static com.io7m.northpike.strings.NPStringConstants.LIMIT;
import static com.io7m.northpike.strings.NPStringConstants.RECEIVED;

/**
 * Functions to create server exceptions.
 */

public final class NPServerExceptions
{
  private NPServerExceptions()
  {

  }

  /**
   * A message was received that was too large.
   *
   * @param strings      The string resources
   * @param messageSize  The size of the message
   * @param messageLimit The message limit
   *
   * @return An exception
   */

  public static NPServerException errorTooLarge(
    final NPStrings strings,
    final int messageSize,
    final int messageLimit)
  {
    return new NPServerException(
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

  /**
   * A short read was encountered.
   *
   * @param strings  The string resources
   * @param expected The expected message size
   * @param received The received data size
   *
   * @return An exception
   */

  public static NPServerException errorShortRead(
    final NPStrings strings,
    final int expected,
    final int received)
  {
    return new NPServerException(
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
   * A protocol exception occurred.
   *
   * @param e A protocol exception
   *
   * @return A server exception
   */

  public static NPServerException errorProtocol(
    final NPProtocolException e)
  {
    return new NPServerException(
      e.getMessage(),
      e,
      e.errorCode(),
      e.attributes(),
      e.remediatingAction()
    );
  }

  /**
   * An unexpected message was encountered.
   *
   * @param strings  The string resources
   * @param expected The expected message type
   * @param received The received message type
   *
   * @return An exception
   */

  public static NPServerException errorUnexpectedMessage(
    final NPStrings strings,
    final Class<?> expected,
    final Object received)
  {
    return new NPServerException(
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

  /**
   * An authentication error was encountered.
   *
   * @param strings The string resources
   *
   * @return An exception
   */

  public static NPServerException errorAuthentication(
    final NPStrings strings)
  {
    return new NPServerException(
      strings.format(ERROR_AUTHENTICATION),
      NPStandardErrorCodes.errorAuthentication(),
      Map.of(),
      Optional.empty()
    );
  }
}
