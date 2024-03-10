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

package com.io7m.northpike.agent.shell.internal;

import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.model.agents.NPAgentServerDescription;
import com.io7m.northpike.model.agents.NPAgentServerID;
import com.io7m.northpike.model.tls.NPTLSConfigurationKind;
import com.io7m.northpike.model.tls.NPTLSEnabledClientAnonymous;
import com.io7m.northpike.model.tls.NPTLSEnabledExplicit;
import com.io7m.northpike.model.tls.NPTLSStoreConfiguration;
import com.io7m.northpike.protocol.agent_console.NPACCommandServerGet;
import com.io7m.northpike.protocol.agent_console.NPACCommandServerPut;
import com.io7m.northpike.protocol.agent_console.NPACResponseOK;
import com.io7m.northpike.strings.NPStringConstants;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QParameterNamed01;
import com.io7m.quarrel.core.QParameterNamed1;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType.QConstant;
import com.io7m.repetoir.core.RPServiceDirectoryType;

import java.nio.file.Path;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.UUID;

import static com.io7m.northpike.model.tls.NPTLSDisabled.TLS_DISABLED;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_NONEXISTENT;
import static java.util.Map.entry;

/**
 * "server-set-tls"
 */

public final class NPAShellCmdServerSetTLS
  extends NPAShellCmdAbstractCR<NPACCommandServerPut, NPACResponseOK>
{
  private static final QParameterNamed1<NPAgentServerID> ID =
    new QParameterNamed1<>(
      "--server",
      List.of(),
      new QConstant(
        "The server ID."),
      Optional.empty(),
      NPAgentServerID.class
    );

  private static final QParameterNamed1<NPTLSConfigurationKind> TLS =
    new QParameterNamed1<>(
      "--tls",
      List.of(),
      new QConstant(
        "Set the TLS type."),
      Optional.of(NPTLSConfigurationKind.TLS_DISABLED),
      NPTLSConfigurationKind.class
    );

  private static final QParameterNamed01<Path> TLS_KEYSTORE_FILE =
    new QParameterNamed01<>(
      "--tls-keystore",
      List.of(),
      new QConstant(
        "The TLS keystore."),
      Optional.empty(),
      Path.class
    );

  private static final QParameterNamed01<String> TLS_KEYSTORE_PROVIDER =
    new QParameterNamed01<>(
      "--tls-keystore-provider",
      List.of(),
      new QConstant(
        "The TLS keystore provider."),
      Optional.empty(),
      String.class
    );

  private static final QParameterNamed01<String> TLS_KEYSTORE_TYPE =
    new QParameterNamed01<>(
      "--tls-keystore-type",
      List.of(),
      new QConstant(
        "The TLS keystore type."),
      Optional.empty(),
      String.class
    );

  private static final QParameterNamed01<String> TLS_KEYSTORE_PASSWORD =
    new QParameterNamed01<>(
      "--tls-keystore-password",
      List.of(),
      new QConstant(
        "The TLS keystore password."),
      Optional.of("changeit"),
      String.class
    );

  private static final QParameterNamed01<Path> TLS_TRUSTSTORE_FILE =
    new QParameterNamed01<>(
      "--tls-truststore",
      List.of(),
      new QConstant(
        "The TLS truststore."),
      Optional.empty(),
      Path.class
    );

  private static final QParameterNamed01<String> TLS_TRUSTSTORE_TYPE =
    new QParameterNamed01<>(
      "--tls-truststore-type",
      List.of(),
      new QConstant(
        "The TLS truststore type."),
      Optional.empty(),
      String.class
    );

  private static final QParameterNamed01<String> TLS_TRUSTSTORE_PASSWORD =
    new QParameterNamed01<>(
      "--tls-truststore-password",
      List.of(),
      new QConstant(
        "The TLS truststore password."),
      Optional.of("changeit"),
      String.class
    );

  private static final QParameterNamed01<String> TLS_TRUSTSTORE_PROVIDER =
    new QParameterNamed01<>(
      "--tls-truststore-provider",
      List.of(),
      new QConstant(
        "The TLS truststore provider."),
      Optional.empty(),
      String.class
    );

  /**
   * Construct a command.
   *
   * @param inServices The services
   */

  public NPAShellCmdServerSetTLS(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "server-set-tls",
        new QConstant("Set TLS configuration for an existing server."),
        Optional.empty()
      ),
      NPACCommandServerPut.class,
      NPACResponseOK.class
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of(
      ID,
      TLS,
      TLS_KEYSTORE_FILE,
      TLS_KEYSTORE_PASSWORD,
      TLS_KEYSTORE_PROVIDER,
      TLS_KEYSTORE_TYPE,
      TLS_TRUSTSTORE_FILE,
      TLS_TRUSTSTORE_PASSWORD,
      TLS_TRUSTSTORE_PROVIDER,
      TLS_TRUSTSTORE_TYPE
    );
  }

  @Override
  protected NPACCommandServerPut onCreateCommand(
    final QCommandContextType context)
    throws Exception
  {
    final var id =
      context.parameterValue(ID);
    final var tls =
      context.parameterValue(TLS);

    final var existing =
      this.client()
        .execute(new NPACCommandServerGet(UUID.randomUUID(), id))
        .results()
        .orElseThrow(() -> this.errorServerNonexistent(id));

    final var tlsConfig =
      switch (tls) {
        case TLS_DISABLED -> {
          yield TLS_DISABLED;
        }

        case TLS_ENABLED_CLIENT_ANONYMOUS -> {
          yield new NPTLSEnabledClientAnonymous();
        }

        case TLS_ENABLED_EXPLICIT -> {
          final var keyStoreConfiguration =
            new NPTLSStoreConfiguration(
              context.parameterValueRequireNow(TLS_KEYSTORE_TYPE),
              context.parameterValueRequireNow(TLS_KEYSTORE_PROVIDER),
              context.parameterValueRequireNow(TLS_KEYSTORE_PASSWORD),
              context.parameterValueRequireNow(TLS_KEYSTORE_FILE)
            );
          final var trustStoreConfiguration =
            new NPTLSStoreConfiguration(
              context.parameterValueRequireNow(TLS_TRUSTSTORE_TYPE),
              context.parameterValueRequireNow(TLS_TRUSTSTORE_PROVIDER),
              context.parameterValueRequireNow(TLS_TRUSTSTORE_PASSWORD),
              context.parameterValueRequireNow(TLS_TRUSTSTORE_FILE)
            );

          yield new NPTLSEnabledExplicit(
            keyStoreConfiguration,
            trustStoreConfiguration
          );
        }
      };

    final NPAgentServerDescription update =
      new NPAgentServerDescription(
        existing.id(),
        existing.hostname(),
        existing.port(),
        tlsConfig,
        existing.messageSizeLimit()
      );

    return new NPACCommandServerPut(UUID.randomUUID(), update);
  }

  private NPException errorServerNonexistent(
    final NPAgentServerID id)
  {
    final var strings =
      this.services().requireService(NPStrings.class);

    return new NPException(
      strings.format(ERROR_NONEXISTENT),
      NPStandardErrorCodes.errorNonexistent(),
      Map.ofEntries(
        entry(strings.format(NPStringConstants.SERVER), id.toString())
      ),
      Optional.empty()
    );
  }

  @Override
  protected void onFormatResponse(
    final QCommandContextType context,
    final NPACResponseOK response)
    throws Exception
  {

  }
}
