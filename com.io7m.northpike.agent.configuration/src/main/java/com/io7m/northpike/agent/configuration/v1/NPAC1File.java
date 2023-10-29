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
import com.io7m.northpike.agent.configuration.NPACFile;

import java.util.Map;
import java.util.stream.Collectors;

/**
 * Element parser.
 */

public final class NPAC1File implements BTElementHandlerType<Object, NPACFile>
{
  private NPAC1AgentList agents;
  private NPAC1ServerList servers;

  /**
   * Element parser.
   *
   * @param context The parse context
   */

  public NPAC1File(
    final BTElementParsingContextType context)
  {

  }

  @Override
  public Map<BTQualifiedName, BTElementHandlerConstructorType<?, ?>>
  onChildHandlersRequested(
    final BTElementParsingContextType context)
  {
    return Map.ofEntries(
      Map.entry(
        NPACv1.element("Agents"),
        NPAC1Agents::new
      ),
      Map.entry(
        NPACv1.element("Servers"),
        NPAC1Servers::new
      )
    );
  }

  @Override
  public void onChildValueProduced(
    final BTElementParsingContextType context,
    final Object result)
  {
    switch (result) {
      case final NPAC1AgentList a -> {
        this.agents = a;
      }
      case final NPAC1ServerList s -> {
        this.servers = s;
      }
      default -> {
        throw new IllegalStateException(
          "Unexpected value: %s".formatted(result)
        );
      }
    }
  }

  @Override
  public NPACFile onElementFinished(
    final BTElementParsingContextType context)
  {
    return new NPACFile(
      this.servers.servers()
        .stream()
        .map(x -> Map.entry(x.id(), x))
        .collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue)),
      this.agents.agents()
        .stream()
        .map(x -> Map.entry(x.name(), x))
        .collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue))
    );
  }
}
