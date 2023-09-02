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

package com.io7m.northpike.server.internal.events;

import com.io7m.northpike.model.NPException;
import com.io7m.northpike.telemetry.api.NPEventServiceType;
import com.io7m.northpike.telemetry.api.NPEventType;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;
import io.opentelemetry.api.common.Attributes;
import io.opentelemetry.api.logs.Severity;
import io.opentelemetry.api.trace.Span;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.slf4j.event.Level;

import java.time.Instant;
import java.util.Objects;
import java.util.concurrent.Flow;
import java.util.concurrent.SubmissionPublisher;

/**
 * The event service.
 */

public final class NPEventService implements NPEventServiceType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPEventService.class);

  private final io.opentelemetry.api.logs.Logger logger;
  private final SubmissionPublisher<NPEventType> events;

  private NPEventService(
    final NPTelemetryServiceType inTelemetry)
  {
    Objects.requireNonNull(inTelemetry, "inTelemetry");

    this.logger =
      inTelemetry.logger();
    this.events =
      new SubmissionPublisher<>();
  }

  /**
   * Create a new event service.
   *
   * @param telemetry The telemetry service
   *
   * @return The event service
   */

  public static NPEventServiceType create(
    final NPTelemetryServiceType telemetry)
  {
    return new NPEventService(telemetry);
  }

  @Override
  public void emit(
    final NPEventType event)
  {
    Objects.requireNonNull(event, "event");

    var builder =
      LOG.makeLoggingEventBuilder(
        switch (event.severity()) {
          case INFO -> Level.INFO;
          case ERROR -> Level.ERROR;
          case WARNING -> Level.WARN;
        }).setMessage(event.message());

    final var eventAttributeBuilder = Attributes.builder();
    for (final var entry : event.asAttributes().entrySet()) {
      eventAttributeBuilder.put(entry.getKey(), entry.getValue());
      builder = builder.addKeyValue(entry.getKey(), entry.getValue());
    }
    builder.log();

    final var attributes = eventAttributeBuilder.build();
    Span.current().addEvent(event.name(), attributes, Instant.now());

    this.logger.logRecordBuilder()
      .setAllAttributes(attributes)
      .setBody(event.message())
      .setSeverity(
        switch (event.severity()) {
          case ERROR -> Severity.ERROR;
          case INFO -> Severity.INFO;
          case WARNING -> Severity.WARN;
        })
      .emit();

    this.events.submit(event);
  }

  @Override
  public Flow.Publisher<NPEventType> events()
  {
    return this.events;
  }

  @Override
  public void close()
    throws NPException
  {
    this.events.close();
  }

  @Override
  public String description()
  {
    return "Event service.";
  }

  @Override
  public String toString()
  {
    return "[NPEventService 0x%s]"
      .formatted(Integer.toUnsignedString(this.hashCode(), 16));
  }
}
