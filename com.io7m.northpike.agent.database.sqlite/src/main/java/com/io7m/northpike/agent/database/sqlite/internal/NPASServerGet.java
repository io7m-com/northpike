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
import com.io7m.northpike.agent.database.sqlite.internal.NPASQueryProviderType.Service;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.model.agents.NPAgentServerDescription;
import com.io7m.northpike.model.agents.NPAgentServerID;
import com.io7m.northpike.model.tls.NPTLSConfigurationKind;
import com.io7m.northpike.model.tls.NPTLSDisabled;
import com.io7m.northpike.model.tls.NPTLSEnabledClientAnonymous;
import com.io7m.northpike.model.tls.NPTLSEnabledExplicit;
import com.io7m.northpike.model.tls.NPTLSStoreConfiguration;
import org.jooq.DSLContext;

import java.io.IOException;
import java.io.StringReader;
import java.nio.file.Path;
import java.util.Map;
import java.util.Optional;
import java.util.Properties;

import static com.io7m.northpike.agent.database.sqlite.internal.tables.Servers.SERVERS;
import static java.util.Objects.requireNonNullElse;

/**
 * Retrieve a server.
 */

public final class NPASServerGet
  extends NPASQAbstract<NPAgentServerID, Optional<NPAgentServerDescription>>
  implements NPAgentDatabaseQueriesServersType.ServerGetType
{
  private static final Service<NPAgentServerID, Optional<NPAgentServerDescription>, ServerGetType> SERVICE =
    new Service<>(ServerGetType.class, NPASServerGet::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPASServerGet(
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
  protected Optional<NPAgentServerDescription> onExecute(
    final DSLContext context,
    final NPAgentServerID server)
    throws NPAgentDatabaseException
  {
    final var result =
      context.select(
          SERVERS.S_ID,
          SERVERS.S_REMOTE_ADDRESS,
          SERVERS.S_PORT,
          SERVERS.S_TLS,
          SERVERS.S_TLS_KEYSTORE,
          SERVERS.S_TLS_TRUSTSTORE,
          SERVERS.S_MESSAGE_SIZE_LIMIT
        ).from(SERVERS)
        .where(SERVERS.S_ID.eq(server.toString()))
        .fetchOptional();

    if (result.isEmpty()) {
      return Optional.empty();
    }

    try {
      return Optional.of(mapRecord(result.get()));
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

  private static NPAgentServerDescription mapRecord(
    final org.jooq.Record record)
    throws IOException
  {
    final var tls =
      switch (NPTLSConfigurationKind.valueOf(record.get(SERVERS.S_TLS))) {
        case NPTLSConfigurationKind.TLS_DISABLED -> {
          yield NPTLSDisabled.TLS_DISABLED;
        }

        case NPTLSConfigurationKind.TLS_ENABLED_CLIENT_ANONYMOUS -> {
          yield new NPTLSEnabledClientAnonymous();
        }

        case NPTLSConfigurationKind.TLS_ENABLED_EXPLICIT -> {
          yield new NPTLSEnabledExplicit(
            parseStore(record.get(SERVERS.S_TLS_KEYSTORE)),
            parseStore(record.get(SERVERS.S_TLS_TRUSTSTORE))
          );
        }
      };

    return new NPAgentServerDescription(
      NPAgentServerID.of(record.get(SERVERS.S_ID)),
      record.get(SERVERS.S_REMOTE_ADDRESS),
      record.<Integer>get(SERVERS.S_PORT).intValue(),
      tls,
      record.<Integer>get(SERVERS.S_MESSAGE_SIZE_LIMIT).intValue()
    );
  }

  private static NPTLSStoreConfiguration parseStore(
    final String text)
    throws IOException
  {
    try (var reader = new StringReader(text)) {
      final var props = new Properties();
      props.load(reader);
      return new NPTLSStoreConfiguration(
        props.getProperty("storeType"),
        props.getProperty("storeProvider"),
        props.getProperty("storePassword"),
        Path.of(props.getProperty("storePath"))
      );
    }
  }
}
