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

import com.io7m.blackthorne.api.BTElementHandlerConstructorType;
import com.io7m.blackthorne.api.BTElementHandlerType;
import com.io7m.blackthorne.api.BTElementParsingContextType;
import com.io7m.blackthorne.api.BTQualifiedName;
import com.io7m.blackthorne.api.Blackthorne;
import com.io7m.jlexing.core.LexicalPosition;
import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.toolexec.NPTXEFalse;
import com.io7m.northpike.toolexec.NPTXEIsEqual;
import com.io7m.northpike.toolexec.NPTXENumber;
import com.io7m.northpike.toolexec.NPTXEString;
import com.io7m.northpike.toolexec.NPTXETrue;
import com.io7m.northpike.toolexec.NPTXEVariableBoolean;
import com.io7m.northpike.toolexec.NPTXEVariableNumber;
import com.io7m.northpike.toolexec.NPTXEVariableString;
import com.io7m.northpike.toolexec.NPTXExpressionType;
import org.xml.sax.Locator;

import java.math.BigDecimal;
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
      entry(element("False"), exprFalse()),
      entry(element("IsEqual"), exprIsEqual()),
      entry(element("Number"), exprNumber()),
      entry(element("String"), exprString()),
      entry(element("True"), exprTrue()),
      entry(element("VariableBoolean"), exprVariableBoolean()),
      entry(element("VariableNumber"), exprVariableNumber()),
      entry(element("VariableString"), exprVariableString())
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
   * @return The handler for Number
   */

  public static BTElementHandlerConstructorType<?, NPTXENumber> exprNumber()
  {
    return Blackthorne.forScalarAttribute(
      element("Number"),
      (context, attributes) -> {
        return new NPTXENumber(
          lexical(context.documentLocator()),
          new BigDecimal(attributes.getValue("Value"))
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
   * @return The handler for VariableNumber
   */

  public static BTElementHandlerConstructorType<?, NPTXEVariableNumber> exprVariableNumber()
  {
    return Blackthorne.forScalarAttribute(
      element("VariableNumber"),
      (context, attributes) -> {
        return new NPTXEVariableNumber(
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
}
