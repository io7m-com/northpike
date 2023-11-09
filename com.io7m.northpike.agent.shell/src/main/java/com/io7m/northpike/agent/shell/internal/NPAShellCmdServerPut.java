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
import com.io7m.northpike.protocol.agent_console.NPACCommandServerGet;
import com.io7m.northpike.protocol.agent_console.NPACCommandServerPut;
import com.io7m.northpike.protocol.agent_console.NPACResponseOK;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QException;
import com.io7m.quarrel.core.QParameterNamed01;
import com.io7m.quarrel.core.QParameterNamed1;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType.QConstant;
import com.io7m.repetoir.core.RPServiceDirectoryType;

import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.UUID;

import static com.io7m.northpike.strings.NPStringConstants.ERROR_MISSING_REQUIRED_PARAMETER;
import static com.io7m.northpike.strings.NPStringConstants.PARAMETER;
import static com.io7m.northpike.strings.NPStringConstants.TYPE;
import static java.util.Map.entry;

/**
 * "server-put"
 */

public final class NPAShellCmdServerPut
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

  private static final QParameterNamed01<String> HOSTNAME =
    new QParameterNamed01<>(
      "--hostname",
      List.of(),
      new QConstant(
        "The server hostname."),
      Optional.empty(),
      String.class
    );

  private static final QParameterNamed01<Integer> PORT =
    new QParameterNamed01<>(
      "--port",
      List.of(),
      new QConstant(
        "The server port."),
      Optional.empty(),
      Integer.class
    );

  private static final QParameterNamed01<Integer> MESSAGE_SIZE_LIMIT =
    new QParameterNamed01<>(
      "--message-size-limit",
      List.of(),
      new QConstant(
        "The server message size limit."),
      Optional.empty(),
      Integer.class
    );

  /**
   * Construct a command.
   *
   * @param inServices The services
   */

  public NPAShellCmdServerPut(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "server-put",
        new QConstant("Update an existing server."),
        Optional.empty()
      ),
      NPACCommandServerPut.class,
      NPACResponseOK.class
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of(ID, HOSTNAME, PORT, MESSAGE_SIZE_LIMIT);
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
        .results();

    final NPAgentServerDescription update;
    if (existing.isPresent()) {
      update = createUpdateForExisting(context, existing);
    } else {
      update = createPutForNew(context, id);
    }

    return new NPACCommandServerPut(UUID.randomUUID(), update);
  }

  private static NPAgentServerDescription createPutForNew(
    final QCommandContextType context,
    final NPAgentServerID id)
    throws QException
  {
    return new NPAgentServerDescription(
      id,
      context.parameterValueRequireNow(HOSTNAME),
      context.parameterValueRequireNow(PORT).intValue(),
      NPTLSDisabled.TLS_DISABLED,
      context.parameterValueRequireNow(MESSAGE_SIZE_LIMIT).intValue()
    );
  }

  private static NPAgentServerDescription createUpdateForExisting(
    final QCommandContextType context,
    final Optional<NPAgentServerDescription> existing)
  {
    var update = existing.get();

    {
      final var p = context.parameterValue(HOSTNAME);
      if (p.isPresent()) {
        update = new NPAgentServerDescription(
          update.id(),
          p.get(),
          update.port(),
          update.tls(),
          update.messageSizeLimit()
        );
      }
    }

    {
      final var p = context.parameterValue(PORT);
      if (p.isPresent()) {
        update = new NPAgentServerDescription(
          update.id(),
          update.hostname(),
          p.get().intValue(),
          update.tls(),
          update.messageSizeLimit()
        );
      }
    }

    {
      final var p = context.parameterValue(MESSAGE_SIZE_LIMIT);
      if (p.isPresent()) {
        update = new NPAgentServerDescription(
          update.id(),
          update.hostname(),
          update.port(),
          update.tls(),
          p.get().intValue()
        );
      }
    }

    return update;
  }

  private NPException errorMissingRequiredParameter(
    final QParameterNamedType<?> parameter)
  {
    final var strings =
      this.services().requireService(NPStrings.class);

    return new NPException(
      strings.format(ERROR_MISSING_REQUIRED_PARAMETER),
      NPStandardErrorCodes.errorConfiguration(),
      Map.ofEntries(
        entry(strings.format(PARAMETER), parameter.name()),
        entry(strings.format(TYPE), parameter.type().getCanonicalName())
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
