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


package com.io7m.northpike.tests;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.InetAddress;
import java.net.Socket;
import java.net.SocketAddress;
import java.net.SocketOption;
import java.net.UnknownHostException;
import java.nio.channels.SocketChannel;
import java.util.Objects;
import java.util.Set;

public final class NPFakeSocket extends Socket
{
  private final InputStream inputStream;
  private final OutputStream outputStream;
  private boolean closed;

  public NPFakeSocket(
    final InputStream inInputStream,
    final OutputStream inOutputStream)
  {
    this.inputStream =
      Objects.requireNonNull(inInputStream, "inputStream");
    this.outputStream =
      Objects.requireNonNull(inOutputStream, "outputStream");
  }

  @Override
  public void connect(
    final SocketAddress endpoint)
  {
    throw new IllegalStateException();
  }

  @Override
  public void connect(
    final SocketAddress endpoint,
    final int timeout)
  {
    throw new IllegalStateException();
  }

  @Override
  public void bind(
    final SocketAddress bindpoint)
  {
    throw new IllegalStateException();
  }

  @Override
  public InetAddress getInetAddress()
  {
    try {
      return InetAddress.getLocalHost();
    } catch (final UnknownHostException e) {
      throw new IllegalStateException(e);
    }
  }

  @Override
  public InetAddress getLocalAddress()
  {
    try {
      return InetAddress.getLocalHost();
    } catch (final UnknownHostException e) {
      throw new IllegalStateException(e);
    }
  }

  @Override
  public int getPort()
  {
    return 30000;
  }

  @Override
  public int getLocalPort()
  {
    return 30001;
  }

  @Override
  public SocketAddress getRemoteSocketAddress()
  {
    throw new IllegalStateException();
  }

  @Override
  public SocketAddress getLocalSocketAddress()
  {
    throw new IllegalStateException();
  }

  @Override
  public SocketChannel getChannel()
  {
    throw new IllegalStateException();
  }

  @Override
  public InputStream getInputStream()
  {
    return this.inputStream;
  }

  @Override
  public OutputStream getOutputStream()
  {
    return this.outputStream;
  }

  @Override
  public void setTcpNoDelay(
    final boolean on)
  {
    throw new IllegalStateException();
  }

  @Override
  public boolean getTcpNoDelay()
  {
    throw new IllegalStateException();
  }

  @Override
  public void setSoLinger(
    final boolean on,
    final int linger)
  {
    throw new IllegalStateException();
  }

  @Override
  public int getSoLinger()
  {
    throw new IllegalStateException();
  }

  @Override
  public void sendUrgentData(
    final int data)
  {
    throw new IllegalStateException();
  }

  @Override
  public void setOOBInline(
    final boolean on)
  {
    throw new IllegalStateException();
  }

  @Override
  public boolean getOOBInline()
  {
    throw new IllegalStateException();
  }

  @Override
  public synchronized void setSoTimeout(
    final int timeout)
  {
    throw new IllegalStateException();
  }

  @Override
  public synchronized int getSoTimeout()
  {
    throw new IllegalStateException();
  }

  @Override
  public synchronized void setSendBufferSize(
    final int size)
  {
    throw new IllegalStateException();
  }

  @Override
  public synchronized int getSendBufferSize()
  {
    throw new IllegalStateException();
  }

  @Override
  public synchronized void setReceiveBufferSize(
    final int size)
  {
    throw new IllegalStateException();
  }

  @Override
  public synchronized int getReceiveBufferSize()
  {
    throw new IllegalStateException();
  }

  @Override
  public void setKeepAlive(
    final boolean on)
  {
    throw new IllegalStateException();
  }

  @Override
  public boolean getKeepAlive()
  {
    throw new IllegalStateException();
  }

  @Override
  public void setTrafficClass(
    final int tc)
  {
    throw new IllegalStateException();
  }

  @Override
  public int getTrafficClass()
  {
    throw new IllegalStateException();
  }

  @Override
  public void setReuseAddress(
    final boolean on)
  {
    throw new IllegalStateException();
  }

  @Override
  public boolean getReuseAddress()
  {
    throw new IllegalStateException();
  }

  @Override
  public synchronized void close()
    throws IOException
  {
    this.closed = true;
  }

  @Override
  public void shutdownInput()
  {
    throw new IllegalStateException();
  }

  @Override
  public void shutdownOutput()
  {
    throw new IllegalStateException();
  }

  @Override
  public String toString()
  {
    throw new IllegalStateException();
  }

  @Override
  public boolean isConnected()
  {
    throw new IllegalStateException();
  }

  @Override
  public boolean isBound()
  {
    throw new IllegalStateException();
  }

  @Override
  public boolean isClosed()
  {
    return this.closed;
  }

  @Override
  public boolean isInputShutdown()
  {
    throw new IllegalStateException();
  }

  @Override
  public boolean isOutputShutdown()
  {
    throw new IllegalStateException();
  }

  @Override
  public void setPerformancePreferences(
    final int connectionTime,
    final int latency,
    final int bandwidth)
  {
    throw new IllegalStateException();
  }

  @Override
  public <T> Socket setOption(
    final SocketOption<T> name,
    final T value)
  {
    throw new IllegalStateException();
  }

  @Override
  public <T> T getOption(
    final SocketOption<T> name)
  {
    throw new IllegalStateException();
  }

  @Override
  public Set<SocketOption<?>> supportedOptions()
  {
    throw new IllegalStateException();
  }
}
