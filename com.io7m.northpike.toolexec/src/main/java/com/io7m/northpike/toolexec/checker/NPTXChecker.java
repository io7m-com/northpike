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


package com.io7m.northpike.toolexec.checker;

import com.io7m.jdeferthrow.core.ExceptionTracker;
import com.io7m.northpike.toolexec.model.NPTXDescription;
import com.io7m.northpike.toolexec.model.NPTXEAnd;
import com.io7m.northpike.toolexec.model.NPTXEFalse;
import com.io7m.northpike.toolexec.model.NPTXEIsEqual;
import com.io7m.northpike.toolexec.model.NPTXENot;
import com.io7m.northpike.toolexec.model.NPTXENumber;
import com.io7m.northpike.toolexec.model.NPTXEOr;
import com.io7m.northpike.toolexec.model.NPTXEString;
import com.io7m.northpike.toolexec.model.NPTXETrue;
import com.io7m.northpike.toolexec.model.NPTXEVariableBoolean;
import com.io7m.northpike.toolexec.model.NPTXEVariableNumber;
import com.io7m.northpike.toolexec.model.NPTXEVariableString;
import com.io7m.northpike.toolexec.model.NPTXExpressionType;
import com.io7m.northpike.toolexec.model.NPTXPlanVariableBoolean;
import com.io7m.northpike.toolexec.model.NPTXPlanVariableNumeric;
import com.io7m.northpike.toolexec.model.NPTXPlanVariableString;
import com.io7m.northpike.toolexec.model.NPTXPlanVariableType;
import com.io7m.northpike.toolexec.model.NPTXPlanVariables;
import com.io7m.northpike.toolexec.model.NPTXSArgumentAdd;
import com.io7m.northpike.toolexec.model.NPTXSEnvironmentClear;
import com.io7m.northpike.toolexec.model.NPTXSEnvironmentPass;
import com.io7m.northpike.toolexec.model.NPTXSEnvironmentRemove;
import com.io7m.northpike.toolexec.model.NPTXSEnvironmentSet;
import com.io7m.northpike.toolexec.model.NPTXSIf;
import com.io7m.northpike.toolexec.model.NPTXStatementType;

import java.util.Objects;

import static com.io7m.northpike.strings.NPStringConstants.TYPE_CHECK_CONDITION;
import static com.io7m.northpike.strings.NPStringConstants.TYPE_CHECK_CONDITION_BRANCHES;
import static com.io7m.northpike.strings.NPStringConstants.TYPE_CHECK_EXPRESSION;
import static com.io7m.northpike.strings.NPStringConstants.TYPE_CHECK_PLAN_VARIABLE;
import static com.io7m.northpike.strings.NPStringConstants.TYPE_CHECK_UNDEFINED_VARIABLE;
import static com.io7m.northpike.toolexec.checker.NPTXType.TYPE_BOOLEAN;
import static com.io7m.northpike.toolexec.checker.NPTXType.TYPE_NUMERIC;
import static com.io7m.northpike.toolexec.checker.NPTXType.TYPE_STRING;
import static com.io7m.northpike.toolexec.checker.NPTXType.TYPE_UNIT;

/**
 * A type checker for tool execution descriptions.
 */

public final class NPTXChecker
{
  private NPTXChecker()
  {

  }

  private static NPTXType checkExpressionVariableString(
    final NPTXPlanVariables variables,
    final NPTXEVariableString v)
    throws NPTXCheckerException
  {
    final var pv = variables.variables().get(v.name());
    if (pv == null) {
      throw new NPTXCheckerException(
        TYPE_CHECK_UNDEFINED_VARIABLE,
        v,
        TYPE_STRING,
        TYPE_UNIT
      );
    }

    final var vType = typeOfVariable(pv);
    if (vType != TYPE_STRING) {
      throw new NPTXCheckerException(
        TYPE_CHECK_PLAN_VARIABLE,
        v,
        vType,
        TYPE_STRING
      );
    }
    return TYPE_STRING;
  }

  private static NPTXType checkExpressionVariableNumber(
    final NPTXPlanVariables variables,
    final NPTXEVariableNumber v)
    throws NPTXCheckerException
  {
    final var pv = variables.variables().get(v.name());
    if (pv == null) {
      throw new NPTXCheckerException(
        TYPE_CHECK_UNDEFINED_VARIABLE,
        v,
        TYPE_NUMERIC,
        TYPE_UNIT
      );
    }

    final var vType = typeOfVariable(pv);
    if (vType != TYPE_NUMERIC) {
      throw new NPTXCheckerException(
        TYPE_CHECK_PLAN_VARIABLE,
        v,
        vType,
        TYPE_NUMERIC
      );
    }
    return TYPE_NUMERIC;
  }

  private static NPTXType checkExpressionVariableBoolean(
    final NPTXPlanVariables variables,
    final NPTXEVariableBoolean v)
    throws NPTXCheckerException
  {
    final var pv = variables.variables().get(v.name());
    if (pv == null) {
      throw new NPTXCheckerException(
        TYPE_CHECK_UNDEFINED_VARIABLE,
        v,
        TYPE_BOOLEAN,
        TYPE_UNIT
      );
    }

    final var vType = typeOfVariable(pv);
    if (vType != TYPE_BOOLEAN) {
      throw new NPTXCheckerException(
        TYPE_CHECK_PLAN_VARIABLE,
        v,
        vType,
        TYPE_BOOLEAN
      );
    }
    return TYPE_BOOLEAN;
  }

  private static NPTXType typeOfVariable(
    final NPTXPlanVariableType v)
  {
    if (v instanceof NPTXPlanVariableBoolean) {
      return TYPE_BOOLEAN;
    }
    if (v instanceof NPTXPlanVariableString) {
      return TYPE_STRING;
    }
    if (v instanceof NPTXPlanVariableNumeric) {
      return TYPE_NUMERIC;
    }
    throw new IllegalStateException();
  }

  /**
   * Check the given tool execution description.
   *
   * @param variables   The variables
   * @param description The description
   *
   * @return The type-checked description
   *
   * @throws NPTXCheckerException On type errors
   */

  public static NPTXTypeChecked checkDescription(
    final NPTXPlanVariables variables,
    final NPTXDescription description)
    throws NPTXCheckerException
  {
    Objects.requireNonNull(variables, "variables");
    Objects.requireNonNull(description, "description");

    final var exceptions =
      new ExceptionTracker<NPTXCheckerException>();

    for (final var statement : description.statements()) {
      try {
        checkStatement(variables, statement);
      } catch (final NPTXCheckerException ex) {
        exceptions.addException(ex);
      }
    }

    exceptions.throwIfNecessary();
    return new NPTXTypeChecked(description, variables);
  }

  /**
   * Check the given statement.
   *
   * @param variables The variables
   * @param statement The statement
   *
   * @return The type of the statement
   *
   * @throws NPTXCheckerException On type errors
   */

  public static NPTXType checkStatement(
    final NPTXPlanVariables variables,
    final NPTXStatementType statement)
    throws NPTXCheckerException
  {
    if (statement instanceof NPTXSArgumentAdd) {
      return TYPE_UNIT;
    }

    if (statement instanceof NPTXSEnvironmentClear) {
      return TYPE_UNIT;
    }

    if (statement instanceof NPTXSEnvironmentPass) {
      return TYPE_UNIT;
    }

    if (statement instanceof NPTXSEnvironmentRemove) {
      return TYPE_UNIT;
    }

    if (statement instanceof NPTXSEnvironmentSet) {
      return TYPE_UNIT;
    }

    if (statement instanceof final NPTXSIf sIf) {
      final var exceptions =
        new ExceptionTracker<NPTXCheckerException>();

      final var t0 =
        checkExpression(variables, sIf.condition());
      if (t0 != TYPE_BOOLEAN) {
        exceptions.addException(
          new NPTXCheckerException(
            TYPE_CHECK_CONDITION,
            sIf.condition(),
            TYPE_BOOLEAN,
            t0
          )
        );
      }

      var tType = TYPE_UNIT;
      final var btSize = sIf.branchTrue().size();
      for (int index = 0; index < btSize; ++index) {
        final var e = sIf.branchTrue().get(index);
        try {
          tType = checkStatement(variables, e);
        } catch (final NPTXCheckerException ex) {
          exceptions.addException(ex);
        }
      }

      var fType = TYPE_UNIT;
      final var bfSize = sIf.branchFalse().size();
      for (int index = 0; index < bfSize; ++index) {
        final var e = sIf.branchFalse().get(index);
        try {
          fType = checkStatement(variables, e);
        } catch (final NPTXCheckerException ex) {
          exceptions.addException(ex);
        }
      }

      if (tType != fType) {
        exceptions.addException(
          new NPTXCheckerException(
            TYPE_CHECK_CONDITION_BRANCHES,
            sIf,
            tType,
            fType
          )
        );
      }
      exceptions.throwIfNecessary();
      return tType;
    }

    throw new IllegalStateException();
  }

  /**
   * Check the given expression.
   *
   * @param variables  The variables
   * @param expression The expression
   *
   * @return The type of the expression
   *
   * @throws NPTXCheckerException On type errors
   */

  public static NPTXType checkExpression(
    final NPTXPlanVariables variables,
    final NPTXExpressionType expression)
    throws NPTXCheckerException
  {
    if (expression instanceof NPTXEFalse) {
      return TYPE_BOOLEAN;
    }

    if (expression instanceof NPTXETrue) {
      return TYPE_BOOLEAN;
    }

    if (expression instanceof NPTXENumber) {
      return TYPE_NUMERIC;
    }

    if (expression instanceof NPTXEString) {
      return TYPE_STRING;
    }

    if (expression instanceof final NPTXEVariableBoolean v) {
      return checkExpressionVariableBoolean(variables, v);
    }

    if (expression instanceof final NPTXEVariableNumber v) {
      return checkExpressionVariableNumber(variables, v);
    }

    if (expression instanceof final NPTXEVariableString v) {
      return checkExpressionVariableString(variables, v);
    }

    if (expression instanceof final NPTXEIsEqual isEqual) {
      return checkExpressionIsEqual(variables, isEqual);
    }

    if (expression instanceof final NPTXEAnd and) {
      return checkExpressionAnd(variables, and);
    }

    if (expression instanceof final NPTXEOr or) {
      return checkExpressionOr(variables, or);
    }

    if (expression instanceof final NPTXENot not) {
      return checkExpressionNot(variables, not);
    }

    throw new IllegalStateException();
  }

  private static NPTXType checkExpressionNot(
    final NPTXPlanVariables variables,
    final NPTXENot not)
    throws NPTXCheckerException
  {
    final var t0 =
      checkExpression(variables, not.e0());

    if (t0 != TYPE_BOOLEAN) {
      throw new NPTXCheckerException(
        TYPE_CHECK_EXPRESSION,
        not.e0(),
        TYPE_BOOLEAN,
        t0
      );
    }

    return TYPE_BOOLEAN;
  }

  private static NPTXType checkExpressionOr(
    final NPTXPlanVariables variables,
    final NPTXEOr or)
    throws NPTXCheckerException
  {
    final var t0 =
      checkExpression(variables, or.e0());
    final var t1 =
      checkExpression(variables, or.e1());

    if (t0 != TYPE_BOOLEAN) {
      throw new NPTXCheckerException(
        TYPE_CHECK_EXPRESSION,
        or.e0(),
        TYPE_BOOLEAN,
        t0
      );
    }

    if (t1 != TYPE_BOOLEAN) {
      throw new NPTXCheckerException(
        TYPE_CHECK_EXPRESSION,
        or.e1(),
        TYPE_BOOLEAN,
        t1
      );
    }

    return TYPE_BOOLEAN;
  }

  private static NPTXType checkExpressionAnd(
    final NPTXPlanVariables variables,
    final NPTXEAnd and)
    throws NPTXCheckerException
  {
    final var t0 =
      checkExpression(variables, and.e0());
    final var t1 =
      checkExpression(variables, and.e1());

    if (t0 != TYPE_BOOLEAN) {
      throw new NPTXCheckerException(
        TYPE_CHECK_EXPRESSION,
        and.e0(),
        TYPE_BOOLEAN,
        t0
      );
    }

    if (t1 != TYPE_BOOLEAN) {
      throw new NPTXCheckerException(
        TYPE_CHECK_EXPRESSION,
        and.e1(),
        TYPE_BOOLEAN,
        t1
      );
    }

    return TYPE_BOOLEAN;
  }

  private static NPTXType checkExpressionIsEqual(
    final NPTXPlanVariables variables,
    final NPTXEIsEqual isEqual)
    throws NPTXCheckerException
  {
    final var t0 =
      checkExpression(variables, isEqual.e0());
    final var t1 =
      checkExpression(variables, isEqual.e1());

    if (t0 != t1) {
      throw new NPTXCheckerException(
        TYPE_CHECK_EXPRESSION,
        isEqual.e1(),
        t0,
        t1
      );
    }
    return TYPE_BOOLEAN;
  }
}
