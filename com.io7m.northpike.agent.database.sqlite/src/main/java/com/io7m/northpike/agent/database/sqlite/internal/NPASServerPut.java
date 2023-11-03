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


package com.io7m.northpike.agent.database.sqlite.internal;

import com.io7m.northpike.agent.database.api.NPAgentDatabaseException;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesServersType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseUnit;
import com.io7m.northpike.agent.database.sqlite.internal.NPASQueryProviderType.Service;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.model.agents.NPAgentServerDescription;
import com.io7m.northpike.model.tls.NPTLSConfigurationType;
import com.io7m.northpike.model.tls.NPTLSDisabled;
import com.io7m.northpike.model.tls.NPTLSEnabled;
import com.io7m.northpike.model.tls.NPTLSStoreConfiguration;
import org.jooq.DSLContext;

import java.io.IOException;
import java.io.StringWriter;
import java.util.Map;
import java.util.Optional;
import java.util.Properties;

import static com.io7m.northpike.agent.database.api.NPAgentDatabaseUnit.UNIT;
import static com.io7m.northpike.agent.database.sqlite.internal.Tables.SERVERS;
import static java.util.Objects.requireNonNullElse;

/**
 * Update a server.
 */

public final class NPASServerPut
  extends NPASQAbstract<NPAgentServerDescription, NPAgentDatabaseUnit>
  implements NPAgentDatabaseQueriesServersType.ServerPutType
{
  private static final Service<NPAgentServerDescription, NPAgentDatabaseUnit, ServerPutType> SERVICE =
    new Service<>(ServerPutType.class, NPASServerPut::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPASServerPut(
    final NPASTransaction transaction)
  {
    super(transaction);
  }

  /**
   * @return A query provider
   */

  public static NPASQueryProviderType provider()
  {
    return () -> SERVICE;
  }

  @Override
  protected NPAgentDatabaseUnit onExecute(
    final DSLContext context,
    final NPAgentServerDescription server)
    throws NPAgentDatabaseException
  {
    try {
      final var query =
        context.insertInto(SERVERS)
          .set(
            SERVERS.S_ID,
            server.id().toString())
          .set(
            SERVERS.S_REMOTE_ADDRESS,
            server.hostname())
          .set(
            SERVERS.S_PORT,
            Integer.valueOf(server.port()))
          .set(
            SERVERS.S_TLS,
            Integer.valueOf(tlsEnabled(server.tls())))
          .set(
            SERVERS.S_TLS_KEYSTORE,
            tlsKeystore(server.tls()))
          .set(
            SERVERS.S_TLS_TRUSTSTORE,
            tlsTruststore(server.tls()))
          .set(
            SERVERS.S_MESSAGE_SIZE_LIMIT,
            Integer.valueOf(server.messageSizeLimit()))
          .onDuplicateKeyUpdate()
          .set(
            SERVERS.S_ID,
            server.id().toString())
          .set(
            SERVERS.S_REMOTE_ADDRESS,
            server.hostname())
          .set(
            SERVERS.S_PORT,
            Integer.valueOf(server.port()))
          .set(
            SERVERS.S_TLS,
            Integer.valueOf(tlsEnabled(server.tls())))
          .set(
            SERVERS.S_TLS_KEYSTORE,
            tlsKeystore(server.tls()))
          .set(
            SERVERS.S_TLS_TRUSTSTORE,
            tlsTruststore(server.tls()))
          .set(
            SERVERS.S_MESSAGE_SIZE_LIMIT,
            Integer.valueOf(server.messageSizeLimit()));

      recordQuery(query);
      query.execute();
      return UNIT;
    } catch (final IOException e) {
      throw new NPAgentDatabaseException(
        requireNonNullElse(e.getMessage(), e.getClass().getCanonicalName()),
        e,
        NPStandardErrorCodes.errorIo(),
        Map.of(),
        Optional.empty()
      );
    }
  }

  private static String tlsTruststore(
    final NPTLSConfigurationType tls)
    throws IOException
  {
    return switch (tls) {
      case final NPTLSDisabled d -> null;
      case final NPTLSEnabled e -> store(e.trustStore());
    };
  }

  private static String tlsKeystore(
    final NPTLSConfigurationType tls)
    throws IOException
  {
    return switch (tls) {
      case final NPTLSDisabled d -> null;
      case final NPTLSEnabled e -> store(e.keyStore());
    };
  }

  private static String store(
    final NPTLSStoreConfiguration configuration)
    throws IOException
  {
    try (var writer = new StringWriter()) {
      final var props = new Properties();
      props.setProperty("storeType", configuration.storeType());
      props.setProperty("storeProvider", configuration.storeProvider());
      props.setProperty("storePassword", configuration.storePassword());
      props.setProperty("storePath", configuration.storePath().toString());
      props.store(writer, "");
      writer.flush();
      return writer.toString();
    }
  }

  private static int tlsEnabled(
    final NPTLSConfigurationType tls)
  {
    return switch (tls) {
      case final NPTLSDisabled d -> 0;
      case final NPTLSEnabled e -> 1;
    };
  }
}
