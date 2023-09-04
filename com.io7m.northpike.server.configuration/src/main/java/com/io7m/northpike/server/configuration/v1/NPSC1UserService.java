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


package com.io7m.northpike.server.configuration.v1;

import com.io7m.blackthorne.core.BTElementHandlerConstructorType;
import com.io7m.blackthorne.core.BTElementHandlerType;
import com.io7m.blackthorne.core.BTElementParsingContextType;
import com.io7m.blackthorne.core.BTQualifiedName;
import com.io7m.northpike.server.api.NPServerUserConfiguration;
import com.io7m.northpike.tls.NPTLS;
import com.io7m.northpike.tls.NPTLSConfigurationType;
import org.xml.sax.Attributes;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Map;
import java.util.Objects;

/**
 * A parser for {@link NPServerUserConfiguration}
 */

public final class NPSC1UserService
  implements BTElementHandlerType<NPTLSConfigurationType, NPServerUserConfiguration>
{
  private InetAddress localAddress;
  private int localPort;
  private int messageSizeLimit;
  private NPTLSConfigurationType tls;

  /**
   * A parser for {@link NPServerUserConfiguration}
   *
   * @param context The parse context
   */

  public NPSC1UserService(
    final BTElementParsingContextType context)
  {

  }

  @Override
  public Map<BTQualifiedName, BTElementHandlerConstructorType<?, ? extends NPTLSConfigurationType>>
  onChildHandlersRequested(
    final BTElementParsingContextType context)
  {
    return NPTLS.configurationElements();
  }

  @Override
  public void onChildValueProduced(
    final BTElementParsingContextType context,
    final NPTLSConfigurationType result)
  {
    this.tls = Objects.requireNonNull(result, "result");
  }

  @Override
  public void onElementStart(
    final BTElementParsingContextType context,
    final Attributes attributes)
    throws UnknownHostException
  {
    this.localAddress =
      InetAddress.getByName(
        attributes.getValue("ListenAddress"));
    this.localPort =
      Integer.parseUnsignedInt(
        attributes.getValue("ListenPort"));
    this.messageSizeLimit =
      Integer.parseUnsignedInt(
        attributes.getValue("MaximumCommandSizeOctets"));
  }

  @Override
  public NPServerUserConfiguration onElementFinished(
    final BTElementParsingContextType context)
  {
    return new NPServerUserConfiguration(
      this.localAddress,
      this.localPort,
      this.tls,
      this.messageSizeLimit
    );
  }
}
