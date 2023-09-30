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


package com.io7m.northpike.tests.shell;

import org.jline.terminal.Attributes;
import org.jline.terminal.Cursor;
import org.jline.terminal.MouseEvent;
import org.jline.terminal.Size;
import org.jline.terminal.Terminal;
import org.jline.utils.ColorPalette;
import org.jline.utils.InfoCmp;
import org.jline.utils.NonBlockingReader;
import org.jline.utils.NonBlockingReaderImpl;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.PipedInputStream;
import java.io.PipedOutputStream;
import java.io.PrintWriter;
import java.nio.charset.Charset;
import java.util.function.IntConsumer;
import java.util.function.IntSupplier;

public final class NPFakeTerminal implements Terminal
{
  private final ByteArrayOutputStream output;
  private final PrintWriter outputWriter;
  private final PipedOutputStream inputStream;
  private final PipedInputStream inputReadStream;
  private final NonBlockingReaderImpl inputReader;
  private final PrintWriter inputWriter;
  private Attributes attributes;

  public NPFakeTerminal()
    throws IOException
  {
    this.attributes =
      new Attributes();

    this.output =
      new ByteArrayOutputStream();
    this.outputWriter =
      new PrintWriter(this.output, true);

    this.inputStream =
      new PipedOutputStream();
    this.inputWriter =
      new PrintWriter(this.inputStream, true);

    this.inputReadStream =
      new PipedInputStream(this.inputStream);
    this.inputReader =
      new NonBlockingReaderImpl(
        "input",
        new InputStreamReader(this.inputReadStream)
      );
  }

  public ByteArrayOutputStream terminalProducedOutput()
  {
    return this.output;
  }

  public PrintWriter sendInputToTerminalWriter()
  {
    return this.inputWriter;
  }

  public OutputStream sendInputToTerminalStream()
  {
    return this.inputStream;
  }

  @Override
  public String getName()
  {
    throw new IllegalStateException();
  }

  @Override
  public SignalHandler handle(
    final Signal signal,
    final SignalHandler handler)
  {
    return null;
  }

  @Override
  public void raise(
    final Signal signal)
  {
    throw new IllegalStateException();
  }

  @Override
  public NonBlockingReader reader()
  {
    return this.inputReader;
  }

  @Override
  public PrintWriter writer()
  {
    return this.outputWriter;
  }

  @Override
  public Charset encoding()
  {
    throw new IllegalStateException();
  }

  @Override
  public InputStream input()
  {
    throw new IllegalStateException();
  }

  @Override
  public OutputStream output()
  {
    return this.output;
  }

  @Override
  public boolean canPauseResume()
  {
    throw new IllegalStateException();
  }

  @Override
  public void pause()
  {
    throw new IllegalStateException();
  }

  @Override
  public void pause(final boolean wait)
    throws InterruptedException
  {
    throw new IllegalStateException();
  }

  @Override
  public void resume()
  {
    throw new IllegalStateException();
  }

  @Override
  public boolean paused()
  {
    throw new IllegalStateException();
  }

  @Override
  public Attributes enterRawMode()
  {
    return this.attributes;
  }

  @Override
  public boolean echo()
  {
    throw new IllegalStateException();
  }

  @Override
  public boolean echo(final boolean echo)
  {
    throw new IllegalStateException();
  }

  @Override
  public Attributes getAttributes()
  {
    return this.attributes;
  }

  @Override
  public void setAttributes(
    final Attributes attr)
  {
    this.attributes = attr;
  }

  @Override
  public Size getSize()
  {
    return new Size(80, 25);
  }

  @Override
  public void setSize(final Size size)
  {

  }

  @Override
  public void flush()
  {

  }

  @Override
  public String getType()
  {
    return null;
  }

  @Override
  public boolean puts(
    final InfoCmp.Capability capability,
    final Object... params)
  {
    return false;
  }

  @Override
  public boolean getBooleanCapability(
    final InfoCmp.Capability capability)
  {
    return false;
  }

  @Override
  public Integer getNumericCapability(
    final InfoCmp.Capability capability)
  {
    return null;
  }

  @Override
  public String getStringCapability(
    final InfoCmp.Capability capability)
  {
    return null;
  }

  @Override
  public Cursor getCursorPosition(
    final IntConsumer discarded)
  {
    throw new IllegalStateException();
  }

  @Override
  public boolean hasMouseSupport()
  {
    throw new IllegalStateException();
  }

  @Override
  public boolean trackMouse(
    final MouseTracking tracking)
  {
    return false;
  }

  @Override
  public MouseEvent readMouseEvent()
  {
    throw new IllegalStateException();
  }

  @Override
  public MouseEvent readMouseEvent(
    final IntSupplier reader)
  {
    throw new IllegalStateException();
  }

  @Override
  public boolean hasFocusSupport()
  {
    throw new IllegalStateException();
  }

  @Override
  public boolean trackFocus(
    final boolean tracking)
  {
    throw new IllegalStateException();
  }

  @Override
  public ColorPalette getPalette()
  {
    return ColorPalette.DEFAULT;
  }

  @Override
  public void close()
    throws IOException
  {

  }
}
