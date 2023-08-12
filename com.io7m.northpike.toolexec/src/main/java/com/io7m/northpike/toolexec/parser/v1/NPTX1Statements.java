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

package com.io7m.northpike.toolexec.parser.v1;

import com.io7m.blackthorne.core.BTElementHandlerConstructorType;
import com.io7m.blackthorne.core.BTElementHandlerType;
import com.io7m.blackthorne.core.BTElementParsingContextType;
import com.io7m.blackthorne.core.BTQualifiedName;
import com.io7m.blackthorne.core.Blackthorne;
import com.io7m.northpike.toolexec.model.NPTXComment;
import com.io7m.northpike.toolexec.model.NPTXExpressionType;
import com.io7m.northpike.toolexec.model.NPTXSArgumentAdd;
import com.io7m.northpike.toolexec.model.NPTXSEnvironmentClear;
import com.io7m.northpike.toolexec.model.NPTXSEnvironmentPass;
import com.io7m.northpike.toolexec.model.NPTXSEnvironmentRemove;
import com.io7m.northpike.toolexec.model.NPTXSEnvironmentSet;
import com.io7m.northpike.toolexec.model.NPTXSIf;
import com.io7m.northpike.toolexec.model.NPTXStatementType;

import java.util.List;
import java.util.Map;

import static com.io7m.blackthorne.core.BTIgnoreUnrecognizedElements.DO_NOT_IGNORE_UNRECOGNIZED_ELEMENTS;
import static com.io7m.northpike.toolexec.parser.v1.NPTX1.element;
import static com.io7m.northpike.toolexec.parser.v1.NPTX1Expressions.expressions;
import static com.io7m.northpike.toolexec.parser.v1.NPTX1Expressions.lexical;

/**
 * XML element handlers for statements.
 */

public final class NPTX1Statements
{
  private static final Map<BTQualifiedName, BTElementHandlerConstructorType<?, ? extends NPTXStatementType>>
    STATEMENT_HANDLERS =
    Map.ofEntries(
      Map.entry(element("ArgumentAdd"), stArgumentAdd()),
      Map.entry(element("Comment"), stComment()),
      Map.entry(element("EnvironmentClear"), stEnvironmentClear()),
      Map.entry(element("EnvironmentPass"), stEnvironmentPass()),
      Map.entry(element("EnvironmentRemove"), stEnvironmentRemove()),
      Map.entry(element("EnvironmentSet"), stEnvironmentSet()),
      Map.entry(element("If"), stIf())
    );

  private NPTX1Statements()
  {

  }

  /**
   * @return The set of handlers for all statement types
   */

  public static Map<BTQualifiedName, BTElementHandlerConstructorType<?, ? extends NPTXStatementType>> statements()
  {
    return STATEMENT_HANDLERS;
  }

  /**
   * @return The handler for If
   */

  public static BTElementHandlerConstructorType<?, NPTXSIf> stIf()
  {
    return IfHandler::new;
  }

  /**
   * @return The handler for ArgumentAdd
   */

  public static BTElementHandlerConstructorType<?, NPTXSArgumentAdd> stArgumentAdd()
  {
    return Blackthorne.forScalarAttribute(
      element("ArgumentAdd"),
      (context, attributes) -> {
        return new NPTXSArgumentAdd(
          lexical(context.documentLocator()),
          attributes.getValue("Value")
        );
      }
    );
  }

  /**
   * @return The handler for Comment
   */

  public static BTElementHandlerConstructorType<?, NPTXComment> stComment()
  {
    return Blackthorne.forScalar(
      element("Comment"),
      (context, characters, offset, length) -> {
        return new NPTXComment(
          lexical(context.documentLocator()),
          new String(characters, offset, length)
        );
      });
  }

  /**
   * @return The handler for EnvironmentClear
   */

  public static BTElementHandlerConstructorType<?, NPTXSEnvironmentClear> stEnvironmentClear()
  {
    return Blackthorne.forScalarAttribute(
      element("EnvironmentClear"),
      (context, attributes) -> {
        return new NPTXSEnvironmentClear(
          lexical(context.documentLocator())
        );
      }
    );
  }

  /**
   * @return The handler for EnvironmentPass
   */

  public static BTElementHandlerConstructorType<?, NPTXSEnvironmentPass> stEnvironmentPass()
  {
    return Blackthorne.forScalarAttribute(
      element("EnvironmentPass"),
      (context, attributes) -> {
        return new NPTXSEnvironmentPass(
          lexical(context.documentLocator()),
          attributes.getValue("Name")
        );
      }
    );
  }

  /**
   * @return The handler for EnvironmentRemove
   */

  public static BTElementHandlerConstructorType<?, NPTXSEnvironmentRemove> stEnvironmentRemove()
  {
    return Blackthorne.forScalarAttribute(
      element("EnvironmentRemove"),
      (context, attributes) -> {
        return new NPTXSEnvironmentRemove(
          lexical(context.documentLocator()),
          attributes.getValue("Name")
        );
      }
    );
  }

  /**
   * @return The handler for EnvironmentSet
   */

  public static BTElementHandlerConstructorType<?, NPTXSEnvironmentSet> stEnvironmentSet()
  {
    return Blackthorne.forScalarAttribute(
      element("EnvironmentSet"),
      (context, attributes) -> {
        return new NPTXSEnvironmentSet(
          lexical(context.documentLocator()),
          attributes.getValue("Name"),
          attributes.getValue("Value")
        );
      }
    );
  }

  /**
   * @return The handler for Condition
   */

  private static BTElementHandlerConstructorType<NPTXExpressionType, IfCondition> stCondition()
  {
    return context -> {
      return Blackthorne.forListPoly(
          element("Condition"),
          expressions(),
          DO_NOT_IGNORE_UNRECOGNIZED_ELEMENTS)
        .create(context)
        .map(expressions -> {
          return new IfCondition(expressions.get(0));
        });
    };
  }

  /**
   * @return The handler for Else
   */

  private static BTElementHandlerConstructorType<NPTXStatementType, Else> stElse()
  {
    return context -> {
      return Blackthorne.forListPoly(
          element("Else"),
          statements(),
          DO_NOT_IGNORE_UNRECOGNIZED_ELEMENTS)
        .create(context)
        .map(Else::new);
    };
  }

  /**
   * @return The handler for Then
   */

  private static BTElementHandlerConstructorType<NPTXStatementType, Then> stThen()
  {
    return context -> {
      return Blackthorne.forListPoly(
          element("Then"),
          statements(),
          DO_NOT_IGNORE_UNRECOGNIZED_ELEMENTS)
        .create(context)
        .map(Then::new);
    };
  }

  private sealed interface ThenElseType
  {

  }

  private record IfCondition(
    NPTXExpressionType expression)
    implements ThenElseType
  {

  }

  private record Then(
    List<NPTXStatementType> statements)
    implements ThenElseType
  {

  }

  private record Else(
    List<NPTXStatementType> statements)
    implements ThenElseType
  {

  }

  private static final class IfHandler
    implements BTElementHandlerType<ThenElseType, NPTXSIf>
  {
    private Then rThen;
    private Else rElse;
    private IfCondition rCond;

    IfHandler(
      final BTElementParsingContextType context)
    {
      this.rThen = new Then(List.of());
      this.rElse = new Else(List.of());
    }

    @Override
    public Map<BTQualifiedName, BTElementHandlerConstructorType<?, ? extends ThenElseType>>
    onChildHandlersRequested(
      final BTElementParsingContextType context)
    {
      return Map.ofEntries(
        Map.entry(element("Condition"), stCondition()),
        Map.entry(element("Then"), stThen()),
        Map.entry(element("Else"), stElse())
      );
    }

    @Override
    public void onChildValueProduced(
      final BTElementParsingContextType context,
      final ThenElseType result)
    {
      if (result instanceof final IfCondition cond) {
        this.rCond = cond;
        return;
      }
      if (result instanceof final Then stThen) {
        this.rThen = stThen;
        return;
      }
      if (result instanceof final Else stElse) {
        this.rElse = stElse;
        return;
      }
    }

    @Override
    public NPTXSIf onElementFinished(
      final BTElementParsingContextType context)
    {
      return new NPTXSIf(
        lexical(context.documentLocator()),
        this.rCond.expression,
        this.rThen.statements,
        this.rElse.statements
      );
    }
  }
}
