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

package com.io7m.northpike.connections;

import com.io7m.northpike.model.NPException;
import com.io7m.northpike.protocol.api.NPProtocolMessageType;
import com.io7m.northpike.protocol.api.NPProtocolMessagesType;
import com.io7m.northpike.strings.NPStrings;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.Socket;
import java.util.Objects;
import java.util.Optional;

/**
 * An abstract connection handler.
 *
 * @param <M> The type of messages
 */

public abstract class NPMessageConnectionHandlerAbstract<M extends NPProtocolMessageType>
  implements NPMessageConnectionHandlerType<M>
{
  private final OutputStream output;
  private final NPProtocolMessagesType<M> messages;
  private final NPStrings strings;
  private final int messageSizeLimit;
  private final Socket socket;
  private final InputStream input;

  protected NPMessageConnectionHandlerAbstract(
    final NPProtocolMessagesType<M> inMessages,
    final NPStrings inStrings,
    final int inMessageSizeLimit,
    final Socket inSocket,
    final InputStream inInputStream,
    final OutputStream inOutputStream)
  {
    this.messages =
      Objects.requireNonNull(inMessages, "messages");
    this.strings =
      Objects.requireNonNull(inStrings, "strings");
    this.messageSizeLimit =
      inMessageSizeLimit;
    this.socket =
      Objects.requireNonNull(inSocket, "inCloseable");
    this.input =
      Objects.requireNonNull(inInputStream, "inOutput");
    this.output =
      Objects.requireNonNull(inOutputStream, "inInput");
  }

  protected final NPStrings strings()
  {
    return this.strings;
  }

  @Override
  public final void send(
    final M message)
    throws NPException, IOException
  {
    this.messages.writeLengthPrefixed(this.output, message);
  }

  @Override
  public final void close()
    throws IOException
  {
    this.socket.close();
  }

  @Override
  public final boolean isClosed()
  {
    return this.socket.isClosed();
  }

  @Override
  public final Optional<M> receive()
    throws NPException, IOException
  {
    final var available = this.input.available();
    if (available <= 4) {
      return Optional.empty();
    }

    return Optional.of(
      this.messages.readLengthPrefixed(
        this.strings,
        this.messageSizeLimit,
        this.input
      )
    );
  }
}
