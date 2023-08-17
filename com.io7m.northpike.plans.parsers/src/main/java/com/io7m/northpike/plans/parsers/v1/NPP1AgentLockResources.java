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


package com.io7m.northpike.plans.parsers.v1;

import com.io7m.blackthorne.core.BTElementHandlerConstructorType;
import com.io7m.blackthorne.core.BTElementHandlerType;
import com.io7m.blackthorne.core.BTElementParsingContextType;
import com.io7m.blackthorne.core.BTQualifiedName;
import com.io7m.blackthorne.core.Blackthorne;
import com.io7m.lanark.core.RDottedName;

import java.util.Map;
import java.util.TreeSet;

import static com.io7m.northpike.plans.parsers.v1.NPP1.element;

/**
 * A handler for locked resources.
 */

public final class NPP1AgentLockResources
  implements BTElementHandlerType<RDottedName, NPP1AgentLockResourcesExpression>
{
  private TreeSet<RDottedName> resources = new TreeSet<>();

  /**
   * A handler for locked resources.
   *
   * @param context The parse context
   */

  public NPP1AgentLockResources(
    final BTElementParsingContextType context)
  {

  }

  @Override
  public Map<BTQualifiedName, BTElementHandlerConstructorType<?, ? extends RDottedName>>
  onChildHandlersRequested(
    final BTElementParsingContextType context)
  {
    return Map.ofEntries(
      Map.entry(
        element("Resource"),
        Blackthorne.forScalarAttribute(
          element("Resource"),
          (c, a) -> {
            return new RDottedName(a.getValue("Name"));
          }
        )
      )
    );
  }

  @Override
  public void onChildValueProduced(
    final BTElementParsingContextType context,
    final RDottedName result)
  {
    this.resources.add(result);
  }

  @Override
  public NPP1AgentLockResourcesExpression onElementFinished(
    final BTElementParsingContextType context)
  {
    return new NPP1AgentLockResourcesExpression(this.resources);
  }
}
