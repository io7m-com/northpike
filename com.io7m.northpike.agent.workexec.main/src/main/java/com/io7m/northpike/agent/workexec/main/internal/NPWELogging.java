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
import ch.qos.logback.core.Appender;
import ch.qos.logback.core.ConsoleAppender;
import ch.qos.logback.core.encoder.LayoutWrappingEncoder;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.slf4j.bridge.SLF4JBridgeHandler;
import org.slf4j.event.Level;

/**
 * Functions to configure logging for work execution.
 */

public final class NPWELogging
{
  private NPWELogging()
  {

  }

  /**
   * Configure the initial logging. This routes everything to stderr using
   * a custom layout.
   */

  public static void configureLoggingInitial()
  {
    SLF4JBridgeHandler.install();

    final ch.qos.logback.classic.Logger rootLogger =
      (ch.qos.logback.classic.Logger) LoggerFactory.getLogger(
        Logger.ROOT_LOGGER_NAME
      );

    rootLogger.setLevel(
      ch.qos.logback.classic.Level.convertAnSLF4JLevel(Level.TRACE)
    );

    final var appenderIterator =
      rootLogger.iteratorForAppenders();

    while (appenderIterator.hasNext()) {
      final Appender<ILoggingEvent> appender = appenderIterator.next();
      if (appender instanceof final ConsoleAppender<ILoggingEvent> console) {
        final var encoder = new LayoutWrappingEncoder<ILoggingEvent>();
        encoder.setLayout(new NPWELoggingTextLayout());
        console.setOutputStream(System.err);
        console.setEncoder(encoder);
      }
    }
  }

  /**
   * Reconfigure logging to route all log messages to a structured logger. This
   * is used during work execution to ensure that properly formatted log
   * messages are written to the output for parsing by a supervisor.
   *
   * @param logger The logger
   */

  public static void configureLoggingWork(
    final NPWELoggerType logger)
  {
    final ch.qos.logback.classic.Logger rootLogger =
      (ch.qos.logback.classic.Logger) LoggerFactory.getLogger(
        Logger.ROOT_LOGGER_NAME
      );

    rootLogger.setLevel(
      ch.qos.logback.classic.Level.convertAnSLF4JLevel(Level.TRACE)
    );

    final var appenderIterator =
      rootLogger.iteratorForAppenders();

    while (appenderIterator.hasNext()) {
      final var appender = appenderIterator.next();
      rootLogger.detachAppender(appender);
    }

    logger.setContext(rootLogger.getLoggerContext());
    rootLogger.addAppender(logger);
    logger.start();
  }
}
