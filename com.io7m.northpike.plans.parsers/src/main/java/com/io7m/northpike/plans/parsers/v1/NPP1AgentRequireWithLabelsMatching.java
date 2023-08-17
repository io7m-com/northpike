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
import com.io7m.northpike.agent.expressions.v1.NAE1Expressions;
import com.io7m.northpike.model.NPAgentLabelMatchType;

import java.util.Map;
import java.util.Objects;

/**
 * An element handler for match expressions.
 */

public final class NPP1AgentRequireWithLabelsMatching
  implements BTElementHandlerType<NPAgentLabelMatchType, NPP1AgentRequireWithLabelsMatchingExpression>
{
  private NPAgentLabelMatchType expression;

  /**
   * An element handler for match expressions.
   *
   * @param context The context
   */

  public NPP1AgentRequireWithLabelsMatching(
    final BTElementParsingContextType context)
  {

  }

  @Override
  public Map<BTQualifiedName, BTElementHandlerConstructorType<?, ? extends NPAgentLabelMatchType>>
  onChildHandlersRequested(
    final BTElementParsingContextType context)
  {
    return NAE1Expressions.expressions();
  }

  @Override
  public void onChildValueProduced(
    final BTElementParsingContextType context,
    final NPAgentLabelMatchType result)
  {
    this.expression = Objects.requireNonNull(result, "result");
  }

  @Override
  public NPP1AgentRequireWithLabelsMatchingExpression onElementFinished(
    final BTElementParsingContextType context)
    throws Exception
  {
    return new NPP1AgentRequireWithLabelsMatchingExpression(this.expression);
  }
}
