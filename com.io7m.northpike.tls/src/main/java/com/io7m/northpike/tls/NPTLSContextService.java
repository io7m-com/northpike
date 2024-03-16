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


package com.io7m.northpike.tls;

import com.io7m.northpike.model.tls.NPTLSStoreConfiguration;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;

import java.io.IOException;
import java.security.GeneralSecurityException;
import java.util.Objects;
import java.util.Optional;
import java.util.concurrent.ConcurrentHashMap;

import static com.io7m.northpike.telemetry.api.NPTelemetryServiceType.recordSpanException;

/**
 * The TLS context service.
 */

public final class NPTLSContextService
  implements NPTLSContextServiceType
{
  private final ConcurrentHashMap.KeySetView<NPTLSContext, Boolean> contexts;
  private final NPTelemetryServiceType telemetry;

  private NPTLSContextService(
    final NPTelemetryServiceType inTelemetry)
  {
    this.telemetry =
      Objects.requireNonNull(inTelemetry, "telemetry");
    this.contexts =
      ConcurrentHashMap.newKeySet();
  }

  /**
   * @param telemetry The telemetry service
   *
   * @return A new TLS context service
   */

  public static NPTLSContextServiceType create(
    final NPTelemetryServiceType telemetry)
  {
    return new NPTLSContextService(telemetry);
  }

  @Override
  public NPTLSContext create(
    final String user,
    final NPTLSStoreConfiguration keyStoreConfiguration,
    final NPTLSStoreConfiguration trustStoreConfiguration)
    throws GeneralSecurityException, IOException
  {
    final var newContext =
      NPTLSContext.create(
        user,
        Optional.of(keyStoreConfiguration),
        Optional.of(trustStoreConfiguration)
      );
    this.contexts.add(newContext);
    return newContext;
  }

  @Override
  public NPTLSContext createClientAnonymous(
    final String user)
    throws GeneralSecurityException, IOException
  {
    final var newContext =
      NPTLSContext.create(
        user,
        Optional.empty(),
        Optional.empty()
      );
    this.contexts.add(newContext);
    return newContext;
  }

  @Override
  public void reload()
  {
    final var span =
      this.telemetry.tracer()
        .spanBuilder("ReloadTLSContexts")
        .startSpan();

    try (var ignored = span.makeCurrent()) {
      for (final var context : this.contexts) {
        this.reloadContext(context);
      }
    } finally {
      span.end();
    }
  }

  private void reloadContext(
    final NPTLSContext context)
  {
    final var span =
      this.telemetry.tracer()
        .spanBuilder("ReloadTLSContext")
        .startSpan();

    try (var ignored = span.makeCurrent()) {
      context.reload();
    } catch (final Exception e) {
      recordSpanException(e);
    } finally {
      span.end();
    }
  }

  @Override
  public String toString()
  {
    return "[NPTLSContextService 0x%s]"
      .formatted(Integer.toUnsignedString(this.hashCode(), 16));
  }

  @Override
  public String description()
  {
    return "The TLS context service.";
  }
}
