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


package com.io7m.northpike.parsers;

import com.io7m.jsx.SExpressionType;
import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.model.NPAgentLabelMatchType;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.strings.NPStringConstantType;
import com.io7m.northpike.strings.NPStrings;

import java.util.List;
import java.util.Locale;
import java.util.Map;

import static com.io7m.jlexing.core.LexicalPositions.zero;
import static com.io7m.northpike.model.NPAgentLabelMatchType.AnyLabel.ANY_LABEL;
import static com.io7m.northpike.strings.NPStringConstants.SYNTAX_AGENT_LABEL_MATCH;
import static com.io7m.northpike.strings.NPStringConstants.SYNTAX_AGENT_LABEL_MATCH_AND;
import static com.io7m.northpike.strings.NPStringConstants.SYNTAX_AGENT_LABEL_MATCH_AND_NAME;
import static com.io7m.northpike.strings.NPStringConstants.SYNTAX_AGENT_LABEL_MATCH_ANYLABEL;
import static com.io7m.northpike.strings.NPStringConstants.SYNTAX_AGENT_LABEL_MATCH_ANYLABEL_NAME;
import static com.io7m.northpike.strings.NPStringConstants.SYNTAX_AGENT_LABEL_MATCH_NAME;
import static com.io7m.northpike.strings.NPStringConstants.SYNTAX_AGENT_LABEL_MATCH_OR;
import static com.io7m.northpike.strings.NPStringConstants.SYNTAX_AGENT_LABEL_MATCH_OR_NAME;
import static com.io7m.northpike.strings.NPStringConstants.SYNTAX_AGENT_LABEL_MATCH_SPECIFIC;
import static com.io7m.northpike.strings.NPStringConstants.SYNTAX_AGENT_LABEL_MATCH_SPECIFIC_NAME;
import static java.util.Map.entry;

/**
 * Functions to parse and serialize expressions.
 */

public final class NPAgentLabelMatchExpressions
  extends NPExpressions
{
  private static final Map<NPStringConstantType, NPStringConstantType> SYNTAX =
    Map.ofEntries(
      entry(
        SYNTAX_AGENT_LABEL_MATCH_NAME,
        SYNTAX_AGENT_LABEL_MATCH),
      entry(
        SYNTAX_AGENT_LABEL_MATCH_ANYLABEL_NAME,
        SYNTAX_AGENT_LABEL_MATCH_ANYLABEL),
      entry(
        SYNTAX_AGENT_LABEL_MATCH_SPECIFIC_NAME,
        SYNTAX_AGENT_LABEL_MATCH_SPECIFIC),
      entry(
        SYNTAX_AGENT_LABEL_MATCH_OR_NAME,
        SYNTAX_AGENT_LABEL_MATCH_OR),
      entry(
        SYNTAX_AGENT_LABEL_MATCH_AND_NAME,
        SYNTAX_AGENT_LABEL_MATCH_AND)
    );

  /**
   * Functions to parse and serialize expressions.
   *
   * @param inStrings The string resources
   */

  public NPAgentLabelMatchExpressions(
    final NPStrings inStrings)
  {
    super(inStrings);
  }

  /**
   * Parse a match expression for names.
   *
   * @param text The input text
   *
   * @return A match expression
   *
   * @throws NPException On errors
   */

  public NPAgentLabelMatchType match(
    final String text)
    throws NPException
  {
    return this.matchExpr(NPExpressions.parse(text));
  }

  private NPAgentLabelMatchType matchExpr(
    final SExpressionType expression)
    throws NPException
  {
    if (expression instanceof final SExpressionType.SAtomType atom) {
      return switch (atom.text().toUpperCase(Locale.ROOT)) {
        case "ANY-LABEL" -> {
          yield ANY_LABEL;
        }
        default -> {
          throw this.createParseError(expression);
        }
      };
    }

    if (expression instanceof final SExpressionType.SList list
      && list.size() >= 2
      && list.get(0) instanceof final SExpressionType.SAtomType head) {

      return switch (head.text().toUpperCase(Locale.ROOT)) {
        case "AND" -> {
          yield this.matchExprAnd(list);
        }
        case "OR" -> {
          yield this.matchExprOr(list);
        }
        case "WITH-LABEL" -> {
          yield this.matchExprWithLabel(list);
        }
        default -> throw this.createParseError(head);
      };
    }

    throw this.createParseError(expression);
  }

  private NPAgentLabelMatchType matchExprOr(
    final SExpressionType.SList list)
    throws NPException
  {
    if (list.size() == 3) {
      return new NPAgentLabelMatchType.Or(
        this.matchExpr(list.get(1)),
        this.matchExpr(list.get(2))
      );
    }
    throw this.createParseError(list);
  }

  private NPAgentLabelMatchType matchExprAnd(
    final SExpressionType.SList list)
    throws NPException
  {
    if (list.size() == 3) {
      return new NPAgentLabelMatchType.And(
        this.matchExpr(list.get(1)),
        this.matchExpr(list.get(2))
      );
    }
    throw this.createParseError(list);
  }

  private NPAgentLabelMatchType matchExprWithLabel(
    final SExpressionType.SList list)
    throws NPException
  {
    if (list.size() == 2) {
      return new NPAgentLabelMatchType.Specific(
        this.name(list.get(1))
      );
    }
    throw this.createParseError(list);
  }

  private RDottedName name(
    final SExpressionType expr)
    throws NPException
  {
    if (expr instanceof final SExpressionType.SAtomType atom) {
      try {
        return new RDottedName(atom.text());
      } catch (final Exception e) {
        throw this.createParseError(expr, e);
      }
    }

    throw this.createParseError(expr);
  }

  @Override
  protected Map<NPStringConstantType, NPStringConstantType> syntax()
  {
    return SYNTAX;
  }

  /**
   * Serialize a match expression for labels.
   *
   * @param match The input match
   *
   * @return A match expression
   */

  public SExpressionType matchSerialize(
    final NPAgentLabelMatchType match)
  {
    if (match == ANY_LABEL) {
      return new SExpressionType.SSymbol(zero(), "any-label");
    }

    if (match instanceof final NPAgentLabelMatchType.Specific specific) {
      return new SExpressionType.SList(
        zero(),
        true,
        List.of(
          new SExpressionType.SSymbol(zero(), "with-label"),
          new SExpressionType.SQuotedString(zero(), specific.name().value())
        )
      );
    }

    if (match instanceof final NPAgentLabelMatchType.And and) {
      return new SExpressionType.SList(
        zero(),
        true,
        List.of(
          new SExpressionType.SSymbol(zero(), "and"),
          this.matchSerialize(and.e0()),
          this.matchSerialize(and.e1())
        )
      );
    }

    if (match instanceof final NPAgentLabelMatchType.Or or) {
      return new SExpressionType.SList(
        zero(),
        true,
        List.of(
          new SExpressionType.SSymbol(zero(), "or"),
          this.matchSerialize(or.e0()),
          this.matchSerialize(or.e1())
        )
      );
    }

    throw new IllegalStateException();
  }

  /**
   * Serialize a match expression for labels.
   *
   * @param match The input match
   *
   * @return A match expression
   *
   * @throws NPException On errors
   */

  public String matchSerializeToString(
    final NPAgentLabelMatchType match)
    throws NPException
  {
    return NPExpressions.serialize(this.matchSerialize(match));
  }
}
