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

import com.io7m.jmulticlose.core.CloseableCollection;
import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.protocol.api.NPProtocolMessageType;
import com.io7m.northpike.protocol.api.NPProtocolMessagesType;
import com.io7m.northpike.strings.NPStrings;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.UncheckedIOException;
import java.net.Socket;
import java.util.Objects;
import java.util.Optional;
import java.util.concurrent.ConcurrentLinkedQueue;

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
  private final CloseableCollectionType<IOException> resources;
  private final Thread readerThread;
  private final ConcurrentLinkedQueue<M> inbox;

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
    this.resources =
      CloseableCollection.create(() -> new IOException("Failed to close resources."));

    this.socket =
      this.resources.add(
        Objects.requireNonNull(inSocket, "inCloseable"));
    this.input =
      this.resources.add(
        Objects.requireNonNull(inInputStream, "inInput"));
    this.output =
      this.resources.add(
        Objects.requireNonNull(inOutputStream, "inOutput"));

    this.inbox =
      new ConcurrentLinkedQueue<>();
    this.readerThread =
      Thread.startVirtualThread(this::readLoop);
  }

  private void readLoop()
  {
    while (true) {
      try {
        this.inbox.add(
          this.messages.readLengthPrefixed(
            this.strings,
            this.messageSizeLimit,
            this.input
          )
        );
      } catch (final Throwable e) {
        try {
          this.close();
          return;
        } catch (final IOException ex) {
          throw new UncheckedIOException(ex);
        }
      }
    }
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
    this.resources.close();
  }

  @Override
  public final boolean isClosed()
  {
    return this.socket.isClosed();
  }

  @Override
  public final Optional<M> receive()
  {
    return Optional.ofNullable(this.inbox.poll());
  }
}
