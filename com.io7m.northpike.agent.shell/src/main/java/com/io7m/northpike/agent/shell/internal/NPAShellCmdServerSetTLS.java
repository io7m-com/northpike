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
import com.io7m.northpike.model.tls.NPTLSDisabled;
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

  private static final QParameterNamed1<Boolean> ENABLED =
    new QParameterNamed1<>(
      "--enabled",
      List.of(),
      new QConstant(
        "True if TLS is enabled."),
      Optional.empty(),
      Boolean.class
    );

  private static final QParameterNamed01<String> KS_TYPE =
    new QParameterNamed01<>(
      "--key-store-type",
      List.of(),
      new QConstant(
        "The keystore type."),
      Optional.empty(),
      String.class
    );

  private static final QParameterNamed01<String> KS_PROVIDER =
    new QParameterNamed01<>(
      "--key-store-provider",
      List.of(),
      new QConstant(
        "The keystore provider."),
      Optional.empty(),
      String.class
    );

  private static final QParameterNamed01<String> KS_PASSWORD =
    new QParameterNamed01<>(
      "--key-store-password",
      List.of(),
      new QConstant(
        "The keystore password."),
      Optional.empty(),
      String.class
    );

  private static final QParameterNamed01<Path> KS_PATH =
    new QParameterNamed01<>(
      "--key-store-path",
      List.of(),
      new QConstant(
        "The keystore path."),
      Optional.empty(),
      Path.class
    );

  private static final QParameterNamed01<String> TS_TYPE =
    new QParameterNamed01<>(
      "--trust-store-type",
      List.of(),
      new QConstant(
        "The truststore type."),
      Optional.empty(),
      String.class
    );

  private static final QParameterNamed01<String> TS_PROVIDER =
    new QParameterNamed01<>(
      "--trust-store-provider",
      List.of(),
      new QConstant(
        "The truststore provider."),
      Optional.empty(),
      String.class
    );

  private static final QParameterNamed01<String> TS_PASSWORD =
    new QParameterNamed01<>(
      "--trust-store-password",
      List.of(),
      new QConstant(
        "The truststore password."),
      Optional.empty(),
      String.class
    );

  private static final QParameterNamed01<Path> TS_PATH =
    new QParameterNamed01<>(
      "--trust-store-path",
      List.of(),
      new QConstant(
        "The truststore path."),
      Optional.empty(),
      Path.class
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
      ENABLED,
      ID,
      KS_PASSWORD,
      KS_PATH,
      KS_PROVIDER,
      KS_TYPE,
      TS_PASSWORD,
      TS_PATH,
      TS_PROVIDER,
      TS_TYPE
    );
  }

  @Override
  protected NPACCommandServerPut onCreateCommand(
    final QCommandContextType context)
    throws Exception
  {
    final var id =
      context.parameterValue(ID);

    final var existing =
      this.client()
        .execute(new NPACCommandServerGet(UUID.randomUUID(), id))
        .results()
        .orElseThrow(() -> this.errorServerNonexistent(id));

    final NPAgentServerDescription update;
    if (context.parameterValue(ENABLED).booleanValue()) {
      update = new NPAgentServerDescription(
        existing.id(),
        existing.hostname(),
        existing.port(),
        new NPTLSEnabledExplicit(
          new NPTLSStoreConfiguration(
            context.parameterValueRequireNow(KS_TYPE),
            context.parameterValueRequireNow(KS_PROVIDER),
            context.parameterValueRequireNow(KS_PASSWORD),
            context.parameterValueRequireNow(KS_PATH)
          ),
          new NPTLSStoreConfiguration(
            context.parameterValueRequireNow(TS_TYPE),
            context.parameterValueRequireNow(TS_PROVIDER),
            context.parameterValueRequireNow(TS_PASSWORD),
            context.parameterValueRequireNow(TS_PATH)
          )
        ),
        existing.messageSizeLimit()
      );
    } else {
      update = new NPAgentServerDescription(
        existing.id(),
        existing.hostname(),
        existing.port(),
        NPTLSDisabled.TLS_DISABLED,
        existing.messageSizeLimit()
      );
    }

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
