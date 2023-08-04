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


package com.io7m.northpike.agent.configuration.internal.v1;

import com.io7m.blackthorne.api.BTElementHandlerType;
import com.io7m.blackthorne.api.BTElementParsingContextType;
import com.io7m.northpike.agent.api.NPAgentConfiguration;
import com.io7m.northpike.model.NPKey;
import com.io7m.northpike.strings.NPStrings;
import org.xml.sax.Attributes;

import java.net.InetAddress;
import java.util.Objects;
import java.util.Optional;

/**
 * A configuration parser.
 */

public final class NPAv1ConfigurationParser
  implements BTElementHandlerType<Object, NPAgentConfiguration>
{
  private final NPStrings strings;
  private InetAddress remoteAddress;
  private int remotePort;
  private boolean useTLS;
  private NPKey accessKey;
  private Integer messageSizeLimit;

  /**
   * A configuration parser.
   *
   * @param inStrings The strings
   */

  public NPAv1ConfigurationParser(
    final NPStrings inStrings)
  {
    this.strings = Objects.requireNonNull(inStrings, "strings");
  }

  @Override
  public void onElementStart(
    final BTElementParsingContextType context,
    final Attributes attributes)
    throws Exception
  {
    this.remoteAddress =
      InetAddress.getByName(attributes.getValue("RemoteServer"));
    this.remotePort =
      Integer.parseUnsignedInt(attributes.getValue("RemotePort"));
    this.useTLS =
      Boolean.parseBoolean(attributes.getValue("UseTLS"));
    this.accessKey =
      NPKey.parse(attributes.getValue("SharedKey"));
    this.messageSizeLimit =
      Optional.ofNullable(attributes.getValue("MessageSizeLimit"))
        .map(x -> Integer.parseUnsignedInt(x))
        .orElse(Integer.MAX_VALUE);
  }

  @Override
  public NPAgentConfiguration onElementFinished(
    final BTElementParsingContextType context)
  {
    return new NPAgentConfiguration(
      this.strings,
      this.remoteAddress,
      this.remotePort,
      this.useTLS,
      this.accessKey,
      this.messageSizeLimit
    );
  }
}
