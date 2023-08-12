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


package com.io7m.northpike.agent.expressions.v1;

import com.io7m.blackthorne.core.BTElementHandlerConstructorType;
import com.io7m.blackthorne.core.BTElementHandlerType;
import com.io7m.blackthorne.core.BTElementParsingContextType;
import com.io7m.blackthorne.core.BTQualifiedName;
import com.io7m.blackthorne.core.Blackthorne;
import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.model.NPAgentLabelMatchType;
import com.io7m.northpike.model.NPAgentLabelMatchType.AnyLabel;
import com.io7m.northpike.model.NPAgentLabelMatchType.Specific;

import java.util.Map;

import static com.io7m.northpike.agent.expressions.v1.NAE1.element;
import static java.util.Map.entry;

/**
 * Label match expressions.
 */

public final class NAE1Expressions
{
  private NAE1Expressions()
  {

  }

  private static final Map<
    BTQualifiedName,
    BTElementHandlerConstructorType<?, ? extends NPAgentLabelMatchType>>
    EXPRESSION_HANDLERS =
    Map.ofEntries(
      entry(element("And"), exprAnd()),
      entry(element("Or"), exprOr()),
      entry(element("WithLabel"), exprWithLabel())
    );

  /**
   * @return The expression handlers
   */

  public static Map<
    BTQualifiedName,
    BTElementHandlerConstructorType<?, ? extends NPAgentLabelMatchType>> expressions()
  {
    return EXPRESSION_HANDLERS;
  }

  /**
   * @return The handler for And
   */

  public static BTElementHandlerConstructorType<?, NPAgentLabelMatchType.And> exprAnd()
  {
    return AndHandler::new;
  }

  /**
   * @return The handler for Or
   */

  public static BTElementHandlerConstructorType<?, NPAgentLabelMatchType.Or> exprOr()
  {
    return OrHandler::new;
  }

  /**
   * @return The handler for Specific
   */

  public static BTElementHandlerConstructorType<?, Specific> exprWithLabel()
  {
    return Blackthorne.forScalarAttribute(
      element("WithLabel"),
      (context, attributes) -> {
        return new Specific(new RDottedName(attributes.getValue("Name")));
      });
  }

  /**
   * @return The handler for AnyLabel
   */

  public static BTElementHandlerConstructorType<?, AnyLabel> exprAnyLabel()
  {
    return Blackthorne.forScalarAttribute(
      element("AnyLabel"),
      (context, attributes) -> AnyLabel.ANY_LABEL
    );
  }

  private static final class AndHandler
    implements BTElementHandlerType<NPAgentLabelMatchType, NPAgentLabelMatchType.And>
  {
    private NPAgentLabelMatchType e0;
    private NPAgentLabelMatchType e1;

    AndHandler(
      final BTElementParsingContextType context)
    {

    }

    @Override
    public Map<BTQualifiedName, BTElementHandlerConstructorType<?, ? extends NPAgentLabelMatchType>>
    onChildHandlersRequested(
      final BTElementParsingContextType context)
    {
      return expressions();
    }

    @Override
    public void onChildValueProduced(
      final BTElementParsingContextType context,
      final NPAgentLabelMatchType newResult)
    {
      if (this.e0 == null) {
        this.e0 = newResult;
        return;
      }
      this.e1 = newResult;
    }

    @Override
    public NPAgentLabelMatchType.And onElementFinished(
      final BTElementParsingContextType context)
    {
      return new NPAgentLabelMatchType.And(
        this.e0,
        this.e1
      );
    }
  }

  private static final class OrHandler
    implements BTElementHandlerType<NPAgentLabelMatchType, NPAgentLabelMatchType.Or>
  {
    private NPAgentLabelMatchType e0;
    private NPAgentLabelMatchType e1;

    OrHandler(
      final BTElementParsingContextType context)
    {

    }

    @Override
    public Map<BTQualifiedName, BTElementHandlerConstructorType<?, ? extends NPAgentLabelMatchType>>
    onChildHandlersRequested(
      final BTElementParsingContextType context)
    {
      return expressions();
    }

    @Override
    public void onChildValueProduced(
      final BTElementParsingContextType context,
      final NPAgentLabelMatchType newResult)
    {
      if (this.e0 == null) {
        this.e0 = newResult;
        return;
      }
      this.e1 = newResult;
    }

    @Override
    public NPAgentLabelMatchType.Or onElementFinished(
      final BTElementParsingContextType context)
    {
      return new NPAgentLabelMatchType.Or(
        this.e0,
        this.e1
      );
    }
  }
}
