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
import com.io7m.northpike.agent.workexec.api.NPAWorkEvent;

import java.io.IOException;

/**
 * A structured logger.
 */

public interface NPWELoggerType
  extends Appender<ILoggingEvent>
{
  /**
   * Initialize the logger.
   *
   * @throws IOException On I/O errors
   */

  void initialize()
    throws IOException;

  /**
   * Log an SLF4J event.
   *
   * @param event The event
   *
   * @throws IOException On I/O errors
   */

  void logStatusEvent(
    ILoggingEvent event)
    throws IOException;

  /**
   * Log a work event.
   *
   * @param event The event
   *
   * @throws IOException On I/O errors
   */

  void logWorkEvent(
    NPAWorkEvent event)
    throws IOException;
}
