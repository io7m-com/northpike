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

import com.io7m.blackthorne.core.BTElementHandlerType;
import com.io7m.blackthorne.core.BTElementParsingContextType;
import com.io7m.northpike.telemetry.api.NPTelemetryConfiguration;
import org.xml.sax.Attributes;

import java.net.URISyntaxException;

/**
 * A parser for {@link NPTelemetryConfiguration.NPLogs}
 */

public final class NPSC1Logs
  implements BTElementHandlerType<Object, NPTelemetryConfiguration.NPLogs>
{
  /**
   * A parser for {@link NPTelemetryConfiguration.NPLogs}
   *
   * @param context The parse context
   */

  public NPSC1Logs(
    final BTElementParsingContextType context)
  {

  }

  @Override
  public void onElementStart(
    final BTElementParsingContextType context,
    final Attributes attributes)
    throws URISyntaxException
  {

  }

  @Override
  public NPTelemetryConfiguration.NPLogs onElementFinished(
    final BTElementParsingContextType context)
  {
    return null;
  }
}
