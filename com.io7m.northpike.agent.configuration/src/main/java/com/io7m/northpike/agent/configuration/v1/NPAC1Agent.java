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
import com.io7m.northpike.agent.configuration.NPACAgent;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorConfiguration;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.model.agents.NPAgentServerID;
import org.xml.sax.Attributes;

import java.util.Map;
import java.util.Objects;

/**
 * Element parser.
 */

public final class NPAC1Agent
  implements BTElementHandlerType<NPAWorkExecutorConfiguration, NPACAgent>
{
  private NPAgentLocalName name;
  private NPAgentServerID server;
  private NPAWorkExecutorConfiguration workExecutor;

  /**
   * Element parser.
   *
   * @param context The parse context
   */

  public NPAC1Agent(
    final BTElementParsingContextType context)
  {

  }

  @Override
  public Map<BTQualifiedName, BTElementHandlerConstructorType<?, ? extends NPAWorkExecutorConfiguration>>
  onChildHandlersRequested(
    final BTElementParsingContextType context)
  {
    return Map.ofEntries(
      Map.entry(
        NPACv1.element("WorkExecutor"),
        NPAC1WorkExecutorConfiguration::new
      )
    );
  }

  @Override
  public void onChildValueProduced(
    final BTElementParsingContextType context,
    final NPAWorkExecutorConfiguration result)
  {
    this.workExecutor = Objects.requireNonNull(result, "result");
  }

  @Override
  public void onElementStart(
    final BTElementParsingContextType context,
    final Attributes attributes)
  {
    this.name =
      NPAgentLocalName.of(attributes.getValue("Name"));
    this.server =
      NPAgentServerID.of(attributes.getValue("Server"));
  }

  @Override
  public NPACAgent onElementFinished(
    final BTElementParsingContextType context)
  {
    return new NPACAgent(
      this.name,
      this.server,
      this.workExecutor
    );
  }
}
