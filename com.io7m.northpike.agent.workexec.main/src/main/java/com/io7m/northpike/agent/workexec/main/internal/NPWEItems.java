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


package com.io7m.northpike.agent.workexec.main.internal;

import com.io7m.cedarbridge.runtime.api.CBUUID;
import com.io7m.cedarbridge.runtime.bssio.CBSerializationContextBSSIO;
import com.io7m.jbssio.vanilla.BSSReaders;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.model.agents.NPAgentWorkItem;
import com.io7m.northpike.protocol.agent.NPACommandSWorkSent;
import com.io7m.northpike.protocol.agent.NPAMessageType;
import com.io7m.northpike.protocol.agent.cb.NPA1CommandSWorkSent;
import com.io7m.northpike.protocol.agent.cb.NPA1Messages;
import com.io7m.northpike.strings.NPStrings;

import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;

import static com.io7m.northpike.strings.NPStringConstants.ERROR_PROTOCOL;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_PROTOCOL_UNSUPPORTED;
import static com.io7m.northpike.strings.NPStringConstants.EXPECTED;
import static com.io7m.northpike.strings.NPStringConstants.RECEIVED;
import static com.io7m.northpike.strings.NPStringConstants.VERSION;

/**
 * Convenience functions to read work items.
 */

public final class NPWEItems
{
  private NPWEItems()
  {

  }

  /**
   * Read a serialized work item from the given file.
   *
   * @param strings The strings
   * @param path    The path
   *
   * @return A work item
   *
   * @throws NPException On errors
   * @throws IOException On errors
   */

  public static NPAgentWorkItem readWorkItem(
    final NPStrings strings,
    final Path path)
    throws NPException, IOException
  {
    try (var input = Files.newInputStream(path)) {
      final var context =
        CBSerializationContextBSSIO.createFromInputStream(
          new BSSReaders(),
          input
        );

      final var uuid =
        CBUUID.deserialize(context);
      final var version =
        (int) context.readU32();

      if (!Objects.equals(NPA1Messages.protocolId(), uuid.value())) {
        throw errorUnsupported(strings, uuid, version);
      }

      return switch (version) {
        case 1 -> {
          yield readWorkItemV1(strings, input);
        }
        default -> {
          throw errorUnsupported(strings, uuid, version);
        }
      };
    }
  }

  private static NPAgentWorkItem readWorkItemV1(
    final NPStrings strings,
    final InputStream input)
    throws NPException, IOException
  {
    final var validator =
      new NPA1Messages();
    final var message =
      validator.readLengthPrefixed(strings, 10_000_000, input);

    return switch (message) {
      case final NPACommandSWorkSent c -> {
        yield c.workItem();
      }
      default -> {
        throw errorUnexpectedMessage(strings, message);
      }
    };
  }

  private static NPException errorUnexpectedMessage(
    final NPStrings strings,
    final NPAMessageType message)
  {
    return new NPException(
      strings.format(ERROR_PROTOCOL),
      NPStandardErrorCodes.errorProtocol(),
      Map.ofEntries(
        Map.entry(
          strings.format(EXPECTED),
          NPA1CommandSWorkSent.class.getCanonicalName()
        ),
        Map.entry(
          strings.format(RECEIVED),
          message.getClass().getCanonicalName()
        )
      ),
      Optional.empty()
    );
  }

  private static NPException errorUnsupported(
    final NPStrings strings,
    final CBUUID uuid,
    final int version)
  {
    return new NPException(
      strings.format(ERROR_PROTOCOL_UNSUPPORTED),
      NPStandardErrorCodes.errorProtocol(),
      Map.ofEntries(
        Map.entry(
          strings.format(EXPECTED),
          NPA1Messages.protocolId().toString()
        ),
        Map.entry(
          strings.format(RECEIVED),
          uuid.toString()
        ),
        Map.entry(
          strings.format(VERSION),
          Integer.toUnsignedString(version)
        )
      ),
      Optional.empty()
    );
  }
}
