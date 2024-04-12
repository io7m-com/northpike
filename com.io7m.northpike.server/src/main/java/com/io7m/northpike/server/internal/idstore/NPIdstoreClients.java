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

package com.io7m.northpike.server.internal.idstore;

import com.io7m.idstore.user_client.IdUClients;
import com.io7m.idstore.user_client.api.IdUClientConfiguration;
import com.io7m.idstore.user_client.api.IdUClientException;
import com.io7m.idstore.user_client.api.IdUClientFactoryType;
import com.io7m.idstore.user_client.api.IdUClientType;
import com.io7m.northpike.server.api.NPServerIdstoreConfiguration;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;

import java.net.URI;
import java.time.Clock;
import java.util.Locale;
import java.util.Objects;

/**
 * Idstore clients.
 */

public final class NPIdstoreClients
  implements NPIdstoreClientsType
{
  private final NPServerIdstoreConfiguration idstore;
  private final NPTelemetryServiceType telemetry;
  private final IdUClientFactoryType clients;
  private final Clock clock;
  private final Locale locale;

  private NPIdstoreClients(
    final Clock inClock,
    final Locale inLocale,
    final NPServerIdstoreConfiguration inIdstore,
    final NPTelemetryServiceType inTelemetry,
    final IdUClientFactoryType inClients)
  {
    this.clock =
      Objects.requireNonNull(inClock, "inClock");
    this.locale =
      Objects.requireNonNull(inLocale, "locale");
    this.idstore =
      Objects.requireNonNull(inIdstore, "idstore");
    this.telemetry =
      Objects.requireNonNull(inTelemetry, "telemetry");
    this.clients =
      Objects.requireNonNull(inClients, "clients");
  }

  /**
   * Create an idstore client service.
   *
   * @param inClock The clock
   * @param inLocale The locale
   * @param telemetry The telemetry service
   * @param idstore  The idstore server configuration
   *
   * @return A client service
   */

  public static NPIdstoreClientsType create(
    final Clock inClock,
    final Locale inLocale,
    final NPTelemetryServiceType telemetry,
    final NPServerIdstoreConfiguration idstore)
  {
    Objects.requireNonNull(inClock, "inClock");
    Objects.requireNonNull(inLocale, "inLocale");
    Objects.requireNonNull(idstore, "idstore");

    return new NPIdstoreClients(
      inClock,
      inLocale,
      idstore,
      telemetry,
      new IdUClients()
    );
  }

  @Override
  public IdUClientType createClient()
    throws IdUClientException
  {
    return this.clients.create(
      new IdUClientConfiguration(
        this.telemetry.openTelemetry(),
        this.clock,
        this.locale
      )
    );
  }

  @Override
  public URI baseURI()
  {
    return this.idstore.baseURI();
  }

  @Override
  public String description()
  {
    return "Identity client service.";
  }

  @Override
  public String toString()
  {
    return "[NPIdstoreClients 0x%s]"
      .formatted(Long.toUnsignedString(this.hashCode(), 16));
  }

  @Override
  public URI passwordResetURI()
  {
    return this.idstore.passwordResetURI();
  }
}
