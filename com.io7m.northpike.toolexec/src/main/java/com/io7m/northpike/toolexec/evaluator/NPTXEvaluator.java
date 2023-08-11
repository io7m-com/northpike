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


package com.io7m.northpike.toolexec.evaluator;

import com.io7m.northpike.toolexec.checker.NPTXTypeChecked;
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
import com.io7m.northpike.toolexec.model.NPTXSArgumentAdd;
import com.io7m.northpike.toolexec.model.NPTXSEnvironmentClear;
import com.io7m.northpike.toolexec.model.NPTXSEnvironmentPass;
import com.io7m.northpike.toolexec.model.NPTXSEnvironmentRemove;
import com.io7m.northpike.toolexec.model.NPTXSEnvironmentSet;
import com.io7m.northpike.toolexec.model.NPTXSIf;
import com.io7m.northpike.toolexec.model.NPTXStatementType;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

import static java.lang.Boolean.FALSE;
import static java.lang.Boolean.TRUE;

/**
 * An evaluator for tool execution descriptions.
 */

public final class NPTXEvaluator
{
  private final Map<String, String> environment;
  private final NPTXTypeChecked source;
  private final HashMap<String, String> outputEnvironment;
  private final ArrayList<String> outputArguments;

  /**
   * An evaluator for tool execution descriptions.
   *
   * @param inEnvironment The input environment
   * @param inSource      The input source
   */

  public NPTXEvaluator(
    final Map<String, String> inEnvironment,
    final NPTXTypeChecked inSource)
  {
    this.environment =
      Map.copyOf(Objects.requireNonNull(inEnvironment, "environment"));
    this.source =
      Objects.requireNonNull(inSource, "source");
    this.outputEnvironment =
      new HashMap<>();
    this.outputArguments =
      new ArrayList<String>();
  }

  /**
   * Execute the evaluator.
   *
   * @return The evaluated tool execution description
   */

  public NPTXEvaluation evaluate()
  {
    this.outputArguments.clear();
    this.outputEnvironment.clear();
    this.outputEnvironment.putAll(this.environment);

    this.evaluateStatements(this.source.description().statements());

    return new NPTXEvaluation(
      this.source,
      Map.copyOf(this.outputEnvironment),
      List.copyOf(this.outputArguments)
    );
  }

  private void evaluateStatements(
    final Iterable<NPTXStatementType> statements)
  {
    for (final var statement : statements) {
      this.evaluateStatement(statement);
    }
  }

  private void evaluateStatement(
    final NPTXStatementType statement)
  {
    if (statement instanceof final NPTXSArgumentAdd add) {
      this.evaluateSArgumentAdd(add);
      return;
    }
    if (statement instanceof final NPTXSEnvironmentSet set) {
      this.evaluateSEnvironmentSet(set);
      return;
    }
    if (statement instanceof final NPTXSEnvironmentRemove rm) {
      this.evaluateSEnvironmentRemove(rm);
      return;
    }
    if (statement instanceof final NPTXSEnvironmentPass pass) {
      this.evaluateSEnvironmentPass(pass);
      return;
    }
    if (statement instanceof final NPTXSEnvironmentClear clear) {
      this.evaluateSEnvironmentClear(clear);
      return;
    }
    if (statement instanceof final NPTXSIf sIf) {
      this.evaluateSIf(sIf);
      return;
    }
  }

  private void evaluateSIf(
    final NPTXSIf sIf)
  {
    if (Objects.equals(this.evaluateExpression(sIf.condition()), TRUE)) {
      this.evaluateStatements(sIf.branchTrue());
    } else {
      this.evaluateStatements(sIf.branchFalse());
    }
  }

  private Object evaluateExpression(
    final NPTXExpressionType expression)
  {
    if (expression instanceof NPTXEFalse) {
      return FALSE;
    }

    if (expression instanceof NPTXETrue) {
      return TRUE;
    }

    if (expression instanceof final NPTXENumber e) {
      return e.value();
    }

    if (expression instanceof final NPTXEString e) {
      return e.value();
    }

    if (expression instanceof final NPTXEIsEqual isEqual) {
      final var e0 = this.evaluateExpression(isEqual.e0());
      final var e1 = this.evaluateExpression(isEqual.e1());
      return Boolean.valueOf(Objects.equals(e0, e1));
    }

    if (expression instanceof final NPTXEVariableString v) {
      final var vv = (NPTXPlanVariableString)
        this.source.planVariables().variables().get(v.name());
      return vv.value();
    }

    if (expression instanceof final NPTXEVariableNumber v) {
      final var vv = (NPTXPlanVariableNumeric)
        this.source.planVariables().variables().get(v.name());
      return vv.value();
    }

    if (expression instanceof final NPTXEVariableBoolean v) {
      final var vv = (NPTXPlanVariableBoolean)
        this.source.planVariables().variables().get(v.name());
      return Boolean.valueOf(vv.value());
    }

    if (expression instanceof final NPTXEOr or) {
      final var e0 = this.evaluateExpression(or.e0());
      if (Objects.equals(e0, TRUE)) {
        return TRUE;
      }
      return (Boolean) this.evaluateExpression(or.e1());
    }

    if (expression instanceof final NPTXEAnd and) {
      final var e0 = this.evaluateExpression(and.e0());
      if (Objects.equals(e0, FALSE)) {
        return FALSE;
      }
      return (Boolean) this.evaluateExpression(and.e1());
    }

    if (expression instanceof final NPTXENot not) {
      final var e0 = this.evaluateExpression(not.e0());
      return Boolean.valueOf(!((Boolean) e0).booleanValue());
    }

    throw new IllegalStateException();
  }

  private void evaluateSEnvironmentClear(
    final NPTXSEnvironmentClear clear)
  {
    this.outputEnvironment.clear();
  }

  private void evaluateSEnvironmentPass(
    final NPTXSEnvironmentPass pass)
  {
    final var existing = this.environment.get(pass.name());
    if (existing != null) {
      this.outputEnvironment.put(pass.name(), existing);
    }
  }

  private void evaluateSEnvironmentRemove(
    final NPTXSEnvironmentRemove rm)
  {
    this.outputEnvironment.remove(rm.name());
  }

  private void evaluateSEnvironmentSet(
    final NPTXSEnvironmentSet set)
  {
    this.outputEnvironment.put(set.name(), set.value());
  }

  private void evaluateSArgumentAdd(
    final NPTXSArgumentAdd add)
  {
    this.outputArguments.add(add.value());
  }
}
