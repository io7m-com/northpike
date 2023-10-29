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

import ch.qos.logback.classic.Level;
import ch.qos.logback.classic.spi.LoggingEvent;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.io.UncheckedIOException;
import java.time.Instant;
import java.util.Map;
import java.util.Objects;
import java.util.concurrent.atomic.AtomicBoolean;

import static java.nio.charset.StandardCharsets.UTF_8;

/**
 * A print stream implementation that is intended to be used to hijack anything
 * written to it and post it to a logger instead. This is used to capture any
 * errant writes to stdout/stderr from the code being executed by the
 * work executor.
 */

public final class NPWELoggerPrintStream extends PrintStream
{
  private final NPWELoggerType logger;
  private final ByteArrayOutputStream capturing;
  private final String name;

  private NPWELoggerPrintStream(
    final NPWELoggerType inLogger,
    final ByteArrayOutputStream inCapturing,
    final String inName)
  {
    super(inCapturing, true, UTF_8);

    this.logger =
      Objects.requireNonNull(inLogger, "logger");
    this.capturing =
      Objects.requireNonNull(inCapturing, "capturing");
    this.name =
      Objects.requireNonNull(inName, "name");
  }

  /**
   * Create a new print stream.
   *
   * @param logger The underlying logger
   * @param name The log name
   *
   * @return The print stream
   */

  public static NPWELoggerPrintStream create(
    final String name,
    final NPWELoggerType logger)
  {
    final var capturing =
      new CaptureOutputStream();
    final var stream =
      new NPWELoggerPrintStream(logger, capturing, name);

    final var reentrancy =
      new AtomicBoolean(false);

    capturing.setOnFlush(() -> {
      if (reentrancy.compareAndSet(false, true)) {
        try {
          stream.flush();
        } finally {
          reentrancy.set(false);
        }
      }
    });
    return stream;
  }

  private static final class CaptureOutputStream extends ByteArrayOutputStream
  {
    private Runnable onFlush;

    CaptureOutputStream()
    {

    }

    public void setOnFlush(
      final Runnable inOnFlush)
    {
      this.onFlush = Objects.requireNonNull(inOnFlush, "onFlush");
    }

    @Override
    public void flush()
      throws IOException
    {
      super.flush();
      this.onFlush.run();
    }
  }

  @Override
  public void flush()
  {
    final var captured =
      this.capturing.toString(UTF_8)
        .stripTrailing();

    this.capturing.reset();

    if (captured.isEmpty()) {
      return;
    }

    final var event = new LoggingEvent();
    event.setInstant(Instant.now());
    event.setMessage(captured);
    event.setLoggerName(this.name);
    event.setLevel(Level.INFO);
    event.setMDCPropertyMap(Map.of());

    try {
      this.logger.logStatusEvent(event);
    } catch (final IOException e) {
      throw new UncheckedIOException(e);
    }
  }
}
