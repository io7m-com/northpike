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

package com.io7m.northpike.shell.internal;

import com.io7m.idstore.model.IdName;
import com.io7m.northpike.model.NPStandardServicePorts;
import com.io7m.northpike.model.tls.NPTLSConfigurationKind;
import com.io7m.northpike.model.tls.NPTLSEnabledClientAnonymous;
import com.io7m.northpike.model.tls.NPTLSEnabledExplicit;
import com.io7m.northpike.model.tls.NPTLSStoreConfiguration;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QCommandStatus;
import com.io7m.quarrel.core.QParameterNamed01;
import com.io7m.quarrel.core.QParameterNamed1;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType.QConstant;
import com.io7m.repetoir.core.RPServiceDirectoryType;

import java.net.InetSocketAddress;
import java.nio.file.Path;
import java.util.List;
import java.util.Optional;

import static com.io7m.northpike.model.tls.NPTLSDisabled.TLS_DISABLED;
import static com.io7m.quarrel.core.QCommandStatus.SUCCESS;

/**
 * "login"
 */

public final class NPShellCmdLogin extends NPShellCmdAbstractU
{
  private static final QParameterNamed1<String> SERVER =
    new QParameterNamed1<>(
      "--server",
      List.of(),
      new QConstant(
        "The server hostname."),
      Optional.empty(),
      String.class
    );

  private static final QParameterNamed1<Integer> PORT =
    new QParameterNamed1<>(
      "--port",
      List.of(),
      new QConstant(
        "The server port."),
      Optional.of(Integer.valueOf(NPStandardServicePorts.userServicePort())),
      Integer.class
    );

  private static final QParameterNamed1<String> USERNAME =
    new QParameterNamed1<>(
      "--user",
      List.of(),
      new QConstant(
        "The username."),
      Optional.empty(),
      String.class
    );

  private static final QParameterNamed1<String> PASSWORD =
    new QParameterNamed1<>(
      "--password",
      List.of(),
      new QConstant(
        "The password."),
      Optional.empty(),
      String.class
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

  public NPShellCmdLogin(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "login",
        new QConstant("Log in."),
        Optional.empty()
      )
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of(
      PASSWORD,
      PORT,
      SERVER,
      TLS,
      TLS_KEYSTORE_FILE,
      TLS_KEYSTORE_PASSWORD,
      TLS_KEYSTORE_PROVIDER,
      TLS_KEYSTORE_TYPE,
      TLS_TRUSTSTORE_FILE,
      TLS_TRUSTSTORE_PASSWORD,
      TLS_TRUSTSTORE_PROVIDER,
      TLS_TRUSTSTORE_TYPE,
      USERNAME
    );
  }

  @Override
  public QCommandStatus onExecute(
    final QCommandContextType context)
    throws Exception
  {
    final var server =
      context.parameterValue(SERVER);
    final var port =
      context.parameterValue(PORT);
    final var userName =
      context.parameterValue(USERNAME);
    final var password =
      context.parameterValue(PASSWORD);
    final var tls =
      context.parameterValue(TLS);

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

    this.client()
      .login(
        InetSocketAddress.createUnresolved(server, port.intValue()),
        tlsConfig,
        new IdName(userName),
        password
      );

    return SUCCESS;
  }
}
