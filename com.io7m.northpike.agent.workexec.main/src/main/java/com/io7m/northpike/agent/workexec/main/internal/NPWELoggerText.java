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

import ch.qos.logback.classic.spi.ILoggingEvent;
import ch.qos.logback.classic.spi.IThrowableProxy;
import ch.qos.logback.core.AppenderBase;
import com.io7m.northpike.agent.workexec.api.NPAWorkEvent;
import com.io7m.northpike.model.NPStoredException;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.UncheckedIOException;
import java.util.Objects;
import java.util.TreeMap;
import java.util.concurrent.locks.ReentrantLock;

import static java.nio.charset.StandardCharsets.UTF_8;

/**
 * A text format logger.
 */

public final class NPWELoggerText
  extends AppenderBase<ILoggingEvent>
  implements NPWELoggerType
{
  private final OutputStream output;
  private final BufferedWriter writer;
  private final ReentrantLock writerLock;

  /**
   * Create a new text logger.
   *
   * @param output The output stream
   *
   * @return The text logger
   */

  public static NPWELoggerType create(
    final OutputStream output)
  {
    return new NPWELoggerText(output);
  }

  private NPWELoggerText(
    final OutputStream inOutput)
  {
    this.output =
      Objects.requireNonNull(inOutput, "output");
    this.writer =
      new BufferedWriter(new OutputStreamWriter(this.output, UTF_8));
    this.writerLock =
      new ReentrantLock();
  }

  /**
   * Format a logging event to a string.
   *
   * @param event The event
   *
   * @return The resulting string
   */

  public static String formatEvent(
    final ILoggingEvent event)
  {
    final var text = new StringBuilder(128);
    text.append(event.getLevel());
    text.append(' ');
    text.append(event.getLoggerName());
    text.append(' ');
    text.append(event.getFormattedMessage());
    text.append('\n');

    final var mdc = event.getMDCPropertyMap();
    if (!mdc.isEmpty()) {
      final var mdcSorted = new TreeMap<>(mdc);

      final var keyLength =
        mdcSorted.keySet()
          .stream()
          .mapToInt(String::length)
          .max()
          .orElse(0);

      for (final var entry : mdcSorted.entrySet()) {
        final var key = entry.getKey();
        final var val = entry.getValue();
        text.append("  ");
        text.append(key);
        text.append(" ".repeat(keyLength - key.length()));
        text.append(" : ");
        text.append(val);
        text.append('\n');
      }
    }

    final var throwable = event.getThrowableProxy();
    if (throwable != null) {
      text.append('\n');
      formatThrowableProxy(throwable, text);
    }

    text.append((char) 0x1E);
    return text.toString();
  }

  private static void formatThrowableProxy(
    final IThrowableProxy throwable,
    final StringBuilder text)
  {
    final var stepArray =
      throwable.getStackTraceElementProxyArray();

    text.append(throwable.getClassName());
    text.append(": ");
    text.append(throwable.getMessage());
    text.append('\n');

    for (var index = 0; index < stepArray.length; ++index) {
      final var step = stepArray[index];
      text.append("    ");
      text.append(step.toString());
      text.append('\n');
    }
    text.append('\n');

    for (final var suppressed : throwable.getSuppressed()) {
      text.append("Suppressed:\n");
      formatThrowableProxy(suppressed, text);
    }

    if (throwable.isCyclic()) {
      return;
    }
    if (throwable.getCause() != null) {
      text.append("Caused by:\n");
      formatThrowableProxy(throwable.getCause(), text);
    }
  }

  @Override
  public void initialize()
  {

  }

  @Override
  public void logStatusEvent(
    final ILoggingEvent event)
    throws IOException
  {
    this.writeLocked(formatEvent(event));
  }

  private void writeLocked(
    final String text)
    throws IOException
  {
    this.writerLock.lock();
    try {
      this.writer.append(text);
      this.writer.flush();
    } finally {
      this.writerLock.unlock();
    }
  }

  @Override
  public void logWorkEvent(
    final NPAWorkEvent event)
    throws IOException
  {
    final var text = new StringBuilder(128);
    text.append(event.severity());
    text.append(' ');
    text.append("WORK");
    text.append(' ');
    text.append(event.message());
    text.append('\n');

    final var mdc = event.attributes();
    if (!mdc.isEmpty()) {
      final var mdcSorted = new TreeMap<>(mdc);

      final var keyLength =
        mdcSorted.keySet()
          .stream()
          .mapToInt(String::length)
          .max()
          .orElse(0);

      for (final var entry : mdcSorted.entrySet()) {
        final var key = entry.getKey();
        final var val = entry.getValue();
        text.append("  ");
        text.append(key);
        text.append(" ".repeat(keyLength - key.length()));
        text.append(" : ");
        text.append(val);
        text.append('\n');
      }
    }

    final var throwableOpt = event.exception();
    if (throwableOpt.isPresent()) {
      text.append('\n');
      formatThrowable(throwableOpt.get(), text);
    }

    text.append((char) 0x1E);
    this.writeLocked(text.toString());
  }

  private static void formatThrowable(
    final NPStoredException throwable,
    final StringBuilder text)
  {
    final var stepArray = throwable.stackTrace();
    text.append(throwable.className());
    text.append(": ");
    text.append(throwable.message());
    text.append('\n');

    for (var index = 0; index < stepArray.size(); ++index) {
      final var step = stepArray.get(index);
      text.append("    ");
      text.append(step.toString());
      text.append('\n');
    }
    text.append('\n');

    for (final var suppressed : throwable.suppressed()) {
      text.append("Suppressed:\n");
      formatThrowable(suppressed, text);
    }
    if (throwable.cause().isPresent()) {
      text.append("Caused by:\n");
      formatThrowable(throwable.cause().get(), text);
    }
  }

  @Override
  protected void append(
    final ILoggingEvent event)
  {
    try {
      this.logStatusEvent(event);
    } catch (final IOException e) {
      throw new UncheckedIOException(e);
    }
  }
}
