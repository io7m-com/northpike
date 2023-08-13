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


package com.io7m.northpike.server.configuration.v1;

import com.io7m.blackthorne.core.BTElementHandlerConstructorType;
import com.io7m.blackthorne.core.BTElementHandlerType;
import com.io7m.blackthorne.core.BTElementParsingContextType;
import com.io7m.blackthorne.core.BTQualifiedName;
import com.io7m.northpike.telemetry.api.NPTelemetryConfiguration;
import com.io7m.northpike.telemetry.api.NPTelemetryConfiguration.NPLogs;
import com.io7m.northpike.telemetry.api.NPTelemetryConfiguration.NPMetrics;
import com.io7m.northpike.telemetry.api.NPTelemetryConfiguration.NPTraces;
import org.xml.sax.Attributes;

import java.util.Map;
import java.util.Optional;

import static com.io7m.northpike.server.configuration.v1.NPSCv1.element;
import static java.util.Map.entry;

/**
 * A parser for {@link NPTelemetryConfiguration}
 */

public final class NPSC1OpenTelemetry
  implements BTElementHandlerType<Object, NPTelemetryConfiguration>
{
  private NPLogs logs;
  private NPTraces traces;
  private NPMetrics metrics;
  private String name;

  /**
   * A parser for {@link NPTelemetryConfiguration}
   *
   * @param context The parse context
   */

  public NPSC1OpenTelemetry(
    final BTElementParsingContextType context)
  {

  }

  @Override
  public Map<BTQualifiedName, BTElementHandlerConstructorType<?, ?>>
  onChildHandlersRequested(
    final BTElementParsingContextType context)
  {
    return Map.ofEntries(
      entry(element("Logs"), NPSC1Logs::new),
      entry(element("Metrics"), NPSC1Metrics::new),
      entry(element("Traces"), NPSC1Traces::new)
    );
  }

  @Override
  public void onChildValueProduced(
    final BTElementParsingContextType context,
    final Object result)
  {
    if (result instanceof final NPLogs e) {
      this.logs = e;
      return;
    }
    if (result instanceof final NPTraces e) {
      this.traces = e;
      return;
    }
    if (result instanceof final NPMetrics e) {
      this.metrics = e;
      return;
    }
  }

  @Override
  public void onElementStart(
    final BTElementParsingContextType context,
    final Attributes attributes)
  {
    this.name = attributes.getValue("LogicalServiceName");
  }

  @Override
  public NPTelemetryConfiguration onElementFinished(
    final BTElementParsingContextType context)
  {
    return new NPTelemetryConfiguration(
      this.name,
      Optional.ofNullable(this.logs),
      Optional.ofNullable(this.metrics),
      Optional.ofNullable(this.traces)
    );
  }
}
