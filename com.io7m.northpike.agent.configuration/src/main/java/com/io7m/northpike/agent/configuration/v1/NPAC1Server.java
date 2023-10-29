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


package com.io7m.northpike.agent.configuration.v1;

import com.io7m.blackthorne.core.BTElementHandlerConstructorType;
import com.io7m.blackthorne.core.BTElementHandlerType;
import com.io7m.blackthorne.core.BTElementParsingContextType;
import com.io7m.blackthorne.core.BTQualifiedName;
import com.io7m.northpike.agent.configuration.NPACServer;
import com.io7m.northpike.model.agents.NPAgentServerID;
import com.io7m.northpike.tls.NPTLS;
import com.io7m.northpike.tls.NPTLSConfigurationType;
import org.xml.sax.Attributes;

import java.util.Map;
import java.util.stream.Collectors;

/**
 * Element parser.
 */

public final class NPAC1Server
  implements BTElementHandlerType<Object, NPACServer>
{
  private NPAgentServerID id;
  private String hostName;
  private int port;
  private int messageSizeLimit;
  private NPTLSConfigurationType tls;

  /**
   * Element parser.
   *
   * @param context The parse context
   */

  public NPAC1Server(
    final BTElementParsingContextType context)
  {

  }

  @Override
  public void onElementStart(
    final BTElementParsingContextType context,
    final Attributes attributes)
  {
    this.id =
      NPAgentServerID.of(attributes.getValue("ID"));
    this.hostName =
      attributes.getValue("HostName");
    this.port =
      Integer.parseUnsignedInt(attributes.getValue("Port"));
    this.messageSizeLimit =
      Integer.parseUnsignedInt(attributes.getValue("MessageSizeLimit"));
  }

  @Override
  public void onChildValueProduced(
    final BTElementParsingContextType context,
    final Object result)
  {
    switch (result) {
      case final NPTLSConfigurationType c -> {
        this.tls = c;
      }
      default -> {
        throw new IllegalStateException(
          "Unexpected value: %s".formatted(result)
        );
      }
    }
  }

  @Override
  public Map<BTQualifiedName, BTElementHandlerConstructorType<?, ?>>
  onChildHandlersRequested(
    final BTElementParsingContextType context)
  {
    return NPTLS.configurationElements()
      .entrySet()
      .stream()
      .map(e -> Map.entry(e.getKey(), e.getValue()))
      .collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));
  }

  @Override
  public NPACServer onElementFinished(
    final BTElementParsingContextType context)
  {
    return new NPACServer(
      this.id,
      this.hostName,
      this.port,
      this.messageSizeLimit,
      this.tls
    );
  }
}
