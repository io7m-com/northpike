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
import com.io7m.jlexing.core.LexicalPosition;
import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.toolexec.model.NPTXEAnd;
import com.io7m.northpike.toolexec.model.NPTXEFalse;
import com.io7m.northpike.toolexec.model.NPTXEInteger;
import com.io7m.northpike.toolexec.model.NPTXEIsEqual;
import com.io7m.northpike.toolexec.model.NPTXENot;
import com.io7m.northpike.toolexec.model.NPTXEOr;
import com.io7m.northpike.toolexec.model.NPTXEString;
import com.io7m.northpike.toolexec.model.NPTXEStringSetContains;
import com.io7m.northpike.toolexec.model.NPTXETrue;
import com.io7m.northpike.toolexec.model.NPTXEVariableBoolean;
import com.io7m.northpike.toolexec.model.NPTXEVariableInteger;
import com.io7m.northpike.toolexec.model.NPTXEVariableString;
import com.io7m.northpike.toolexec.model.NPTXEVariableStringSet;
import com.io7m.northpike.toolexec.model.NPTXExpressionType;
import org.xml.sax.Attributes;
import org.xml.sax.Locator;

import java.net.URI;
import java.util.Map;
import java.util.Optional;

import static com.io7m.northpike.toolexec.parser.v1.NPTX1.element;
import static java.util.Map.entry;

/**
 * XML handlers for expression elements.
 */

public final class NPTX1Expressions
{
  private static final Map<
    BTQualifiedName,
    BTElementHandlerConstructorType<?, ? extends NPTXExpressionType>>
    EXPRESSION_HANDLERS =
    Map.ofEntries(
      entry(element("And"), exprAnd()),
      entry(element("False"), exprFalse()),
      entry(element("IsEqual"), exprIsEqual()),
      entry(element("Not"), exprNot()),
      entry(element("Integer"), exprInteger()),
      entry(element("Or"), exprOr()),
      entry(element("String"), exprString()),
      entry(element("StringSetContains"), exprStringSetContains()),
      entry(element("True"), exprTrue()),
      entry(element("VariableBoolean"), exprVariableBoolean()),
      entry(element("VariableInteger"), exprVariableInteger()),
      entry(element("VariableString"), exprVariableString()),
      entry(element("VariableStringSet"), exprVariableStringSet())
    );

  static Map<
    BTQualifiedName,
    BTElementHandlerConstructorType<?, ? extends NPTXExpressionType>> expressions()
  {
    return EXPRESSION_HANDLERS;
  }

  private NPTX1Expressions()
  {

  }

  /**
   * @return The handler for True
   */

  public static BTElementHandlerConstructorType<?, NPTXETrue> exprTrue()
  {
    return Blackthorne.forScalar(
      element("True"),
      (context, characters, offset, length) -> {
        return new NPTXETrue(lexical(context.documentLocator()));
      }
    );
  }

  /**
   * @return The handler for False
   */

  public static BTElementHandlerConstructorType<?, NPTXEFalse> exprFalse()
  {
    return Blackthorne.forScalar(
      element("False"),
      (context, characters, offset, length) -> {
        return new NPTXEFalse(lexical(context.documentLocator()));
      }
    );
  }

  /**
   * @return The handler for Integer
   */

  public static BTElementHandlerConstructorType<?, NPTXEInteger> exprInteger()
  {
    return Blackthorne.forScalarAttribute(
      element("Integer"),
      (context, attributes) -> {
        return new NPTXEInteger(
          lexical(context.documentLocator()),
          Long.parseLong(attributes.getValue("Value"))
        );
      }
    );
  }

  /**
   * @return The handler for String
   */

  public static BTElementHandlerConstructorType<?, NPTXEString> exprString()
  {
    return Blackthorne.forScalarAttribute(
      element("String"),
      (context, attributes) -> {
        return new NPTXEString(
          lexical(context.documentLocator()),
          attributes.getValue("Value")
        );
      }
    );
  }

  /**
   * @return The handler for VariableBoolean
   */

  public static BTElementHandlerConstructorType<?, NPTXEVariableBoolean> exprVariableBoolean()
  {
    return Blackthorne.forScalarAttribute(
      element("VariableBoolean"),
      (context, attributes) -> {
        return new NPTXEVariableBoolean(
          lexical(context.documentLocator()),
          new RDottedName(attributes.getValue("Name"))
        );
      }
    );
  }

  /**
   * @return The handler for VariableStringSet
   */

  public static BTElementHandlerConstructorType<?, NPTXEVariableStringSet> exprVariableStringSet()
  {
    return Blackthorne.forScalarAttribute(
      element("VariableStringSet"),
      (context, attributes) -> {
        return new NPTXEVariableStringSet(
          lexical(context.documentLocator()),
          new RDottedName(attributes.getValue("Name"))
        );
      }
    );
  }

  /**
   * @return The handler for VariableInteger
   */

  public static BTElementHandlerConstructorType<?, NPTXEVariableInteger> exprVariableInteger()
  {
    return Blackthorne.forScalarAttribute(
      element("VariableInteger"),
      (context, attributes) -> {
        return new NPTXEVariableInteger(
          lexical(context.documentLocator()),
          new RDottedName(attributes.getValue("Name"))
        );
      }
    );
  }

  /**
   * @return The handler for VariableString
   */

  public static BTElementHandlerConstructorType<?, NPTXEVariableString> exprVariableString()
  {
    return Blackthorne.forScalarAttribute(
      element("VariableString"),
      (context, attributes) -> {
        return new NPTXEVariableString(
          lexical(context.documentLocator()),
          new RDottedName(attributes.getValue("Name"))
        );
      }
    );
  }

  /**
   * @return The handler for IsEqual
   */

  public static BTElementHandlerConstructorType<?, NPTXEIsEqual> exprIsEqual()
  {
    return IsEqualHandler::new;
  }

  /**
   * @return The handler for And
   */

  public static BTElementHandlerConstructorType<?, NPTXEAnd> exprAnd()
  {
    return AndHandler::new;
  }

  /**
   * @return The handler for Or
   */

  public static BTElementHandlerConstructorType<?, NPTXEOr> exprOr()
  {
    return OrHandler::new;
  }

  /**
   * @return The handler for Not
   */

  public static BTElementHandlerConstructorType<?, NPTXENot> exprNot()
  {
    return NotHandler::new;
  }

  /**
   * @return The handler for StringSetContains
   */

  public static BTElementHandlerConstructorType<?, NPTXEStringSetContains> exprStringSetContains()
  {
    return StringSetContainsHandler::new;
  }

  static LexicalPosition<URI> lexical(
    final Locator locator)
  {
    return LexicalPosition.of(
      locator.getLineNumber(),
      locator.getColumnNumber(),
      Optional.empty()
    );
  }

  private static final class IsEqualHandler
    implements BTElementHandlerType<NPTXExpressionType, NPTXEIsEqual>
  {
    private NPTXExpressionType e0;
    private NPTXExpressionType e1;

    IsEqualHandler(
      final BTElementParsingContextType context)
    {

    }

    @Override
    public Map<BTQualifiedName, BTElementHandlerConstructorType<?, ? extends NPTXExpressionType>>
    onChildHandlersRequested(
      final BTElementParsingContextType context)
    {
      return expressions();
    }

    @Override
    public void onChildValueProduced(
      final BTElementParsingContextType context,
      final NPTXExpressionType newResult)
    {
      if (this.e0 == null) {
        this.e0 = newResult;
        return;
      }
      this.e1 = newResult;
    }

    @Override
    public NPTXEIsEqual onElementFinished(
      final BTElementParsingContextType context)
    {
      return new NPTXEIsEqual(
        lexical(context.documentLocator()),
        this.e0,
        this.e1
      );
    }
  }

  private static final class AndHandler
    implements BTElementHandlerType<NPTXExpressionType, NPTXEAnd>
  {
    private NPTXExpressionType e0;
    private NPTXExpressionType e1;

    AndHandler(
      final BTElementParsingContextType context)
    {

    }

    @Override
    public Map<BTQualifiedName, BTElementHandlerConstructorType<?, ? extends NPTXExpressionType>>
    onChildHandlersRequested(
      final BTElementParsingContextType context)
    {
      return expressions();
    }

    @Override
    public void onChildValueProduced(
      final BTElementParsingContextType context,
      final NPTXExpressionType newResult)
    {
      if (this.e0 == null) {
        this.e0 = newResult;
        return;
      }
      this.e1 = newResult;
    }

    @Override
    public NPTXEAnd onElementFinished(
      final BTElementParsingContextType context)
    {
      return new NPTXEAnd(
        lexical(context.documentLocator()),
        this.e0,
        this.e1
      );
    }
  }

  private static final class OrHandler
    implements BTElementHandlerType<NPTXExpressionType, NPTXEOr>
  {
    private NPTXExpressionType e0;
    private NPTXExpressionType e1;

    OrHandler(
      final BTElementParsingContextType context)
    {

    }

    @Override
    public Map<BTQualifiedName, BTElementHandlerConstructorType<?, ? extends NPTXExpressionType>>
    onChildHandlersRequested(
      final BTElementParsingContextType context)
    {
      return expressions();
    }

    @Override
    public void onChildValueProduced(
      final BTElementParsingContextType context,
      final NPTXExpressionType newResult)
    {
      if (this.e0 == null) {
        this.e0 = newResult;
        return;
      }
      this.e1 = newResult;
    }

    @Override
    public NPTXEOr onElementFinished(
      final BTElementParsingContextType context)
    {
      return new NPTXEOr(
        lexical(context.documentLocator()),
        this.e0,
        this.e1
      );
    }
  }

  private static final class NotHandler
    implements BTElementHandlerType<NPTXExpressionType, NPTXENot>
  {
    private NPTXExpressionType e0;

    NotHandler(
      final BTElementParsingContextType context)
    {

    }

    @Override
    public Map<BTQualifiedName, BTElementHandlerConstructorType<?, ? extends NPTXExpressionType>>
    onChildHandlersRequested(
      final BTElementParsingContextType context)
    {
      return expressions();
    }

    @Override
    public void onChildValueProduced(
      final BTElementParsingContextType context,
      final NPTXExpressionType newResult)
    {
      this.e0 = newResult;
    }

    @Override
    public NPTXENot onElementFinished(
      final BTElementParsingContextType context)
    {
      return new NPTXENot(
        lexical(context.documentLocator()),
        this.e0
      );
    }
  }

  private static final class StringSetContainsHandler
    implements BTElementHandlerType<NPTXExpressionType, NPTXEStringSetContains>
  {
    private NPTXExpressionType e0;
    private String value;

    StringSetContainsHandler(
      final BTElementParsingContextType context)
    {

    }

    @Override
    public Map<BTQualifiedName, BTElementHandlerConstructorType<?, ? extends NPTXExpressionType>>
    onChildHandlersRequested(
      final BTElementParsingContextType context)
    {
      return expressions();
    }

    @Override
    public void onElementStart(
      final BTElementParsingContextType context,
      final Attributes attributes)
    {
      this.value = attributes.getValue("Value");
    }

    @Override
    public void onChildValueProduced(
      final BTElementParsingContextType context,
      final NPTXExpressionType newResult)
    {
      this.e0 = newResult;
    }

    @Override
    public NPTXEStringSetContains onElementFinished(
      final BTElementParsingContextType context)
    {
      return new NPTXEStringSetContains(
        lexical(context.documentLocator()),
        this.value,
        this.e0
      );
    }
  }
}
