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


package com.io7m.northpike.tests.toolexec;

import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.model.NPPreserveLexical;
import com.io7m.northpike.toolexec.checker.NPTXChecker;
import com.io7m.northpike.toolexec.checker.NPTXCheckerException;
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
import com.io7m.northpike.toolexec.model.NPTXPlanVariableBoolean;
import com.io7m.northpike.toolexec.model.NPTXPlanVariableNumeric;
import com.io7m.northpike.toolexec.model.NPTXPlanVariableString;
import com.io7m.northpike.toolexec.model.NPTXPlanVariables;
import com.io7m.northpike.toolexec.model.NPTXSArgumentAdd;
import com.io7m.northpike.toolexec.model.NPTXSEnvironmentClear;
import com.io7m.northpike.toolexec.model.NPTXSEnvironmentPass;
import com.io7m.northpike.toolexec.model.NPTXSEnvironmentRemove;
import com.io7m.northpike.toolexec.model.NPTXSEnvironmentSet;
import com.io7m.northpike.toolexec.model.NPTXSIf;
import com.io7m.northpike.toolexec.parser.NPTXDescriptionParser;
import net.jqwik.api.Example;
import net.jqwik.api.ForAll;
import net.jqwik.api.Property;
import org.junit.jupiter.api.Test;

import java.math.BigInteger;
import java.net.URI;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static com.io7m.jlexing.core.LexicalPositions.zero;
import static com.io7m.northpike.strings.NPStringConstants.TYPE_CHECK_CONDITION;
import static com.io7m.northpike.strings.NPStringConstants.TYPE_CHECK_EXPRESSION;
import static com.io7m.northpike.strings.NPStringConstants.TYPE_CHECK_PLAN_VARIABLE;
import static com.io7m.northpike.strings.NPStringConstants.TYPE_CHECK_UNDEFINED_VARIABLE;
import static com.io7m.northpike.toolexec.checker.NPTXType.TYPE_BOOLEAN;
import static com.io7m.northpike.toolexec.checker.NPTXType.TYPE_NUMERIC;
import static com.io7m.northpike.toolexec.checker.NPTXType.TYPE_STRING;
import static com.io7m.northpike.toolexec.checker.NPTXType.TYPE_UNIT;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

public final class NPTXCheckingTest
{
  @Property
  public void testCheckSArgumentAdd(
    final @ForAll NPTXPlanVariables variables,
    final @ForAll String text)
    throws Exception
  {
    assertEquals(
      TYPE_UNIT,
      NPTXChecker.checkStatement(
        variables,
        new NPTXSArgumentAdd(zero(), text)
      )
    );
  }

  @Property
  public void testCheckSEnvironmentClear(
    final @ForAll NPTXPlanVariables variables)
    throws Exception
  {
    assertEquals(
      TYPE_UNIT,
      NPTXChecker.checkStatement(
        variables,
        new NPTXSEnvironmentClear(zero())
      )
    );
  }

  @Property
  public void testCheckSEnvironmentPass(
    final @ForAll NPTXPlanVariables variables,
    final @ForAll String text)
    throws Exception
  {
    assertEquals(
      TYPE_UNIT,
      NPTXChecker.checkStatement(
        variables,
        new NPTXSEnvironmentPass(zero(), text)
      )
    );
  }

  @Property
  public void testCheckSEnvironmentRemove(
    final @ForAll NPTXPlanVariables variables,
    final @ForAll String text)
    throws Exception
  {
    assertEquals(
      TYPE_UNIT,
      NPTXChecker.checkStatement(
        variables,
        new NPTXSEnvironmentRemove(zero(), text)
      )
    );
  }

  @Property
  public void testCheckSEnvironmentSet(
    final @ForAll NPTXPlanVariables variables,
    final @ForAll String key,
    final @ForAll String val)
    throws Exception
  {
    assertEquals(
      TYPE_UNIT,
      NPTXChecker.checkStatement(
        variables,
        new NPTXSEnvironmentSet(zero(), key, val)
      )
    );
  }

  @Property
  public void testCheckSIf0(
    final @ForAll NPTXPlanVariables variables)
    throws Exception
  {
    assertEquals(
      TYPE_UNIT,
      NPTXChecker.checkStatement(
        variables,
        new NPTXSIf(zero(), new NPTXETrue(zero()), List.of(), List.of())
      )
    );
  }

  @Property
  public void testCheckSIfNotBoolean(
    final @ForAll NPTXPlanVariables variables)
    throws Exception
  {
    final var ex =
      assertThrows(NPTXCheckerException.class, () -> {
        NPTXChecker.checkStatement(
          variables,
          new NPTXSIf(
            zero(),
            new NPTXEString(zero(), "x"),
            List.of(),
            List.of())
        );
      });

    assertEquals(TYPE_CHECK_CONDITION, ex.message());
  }

  @Example
  public void testCheckSIfBadBranches0()
    throws Exception
  {
    final var v2 = new NPTXPlanVariables(Map.of());

    final var if0 =
      new NPTXSIf(
        zero(),
        new NPTXENumber(zero(), BigInteger.ONE),
        List.of(),
        List.of()
      );

    final var if1 =
      new NPTXSIf(
        zero(),
        new NPTXENumber(zero(), BigInteger.ONE),
        List.of(),
        List.of()
      );

    final var ex =
      assertThrows(NPTXCheckerException.class, () -> {
        NPTXChecker.checkStatement(
          v2,
          new NPTXSIf(
            zero(),
            new NPTXETrue(zero()),
            List.of(if0),
            List.of(if1))
        );
      });

    assertEquals(TYPE_CHECK_CONDITION, ex.message());
  }

  @Example
  public void testCheckSIfOKBranches0()
    throws Exception
  {
    final var v2 = new NPTXPlanVariables(Map.of());

    final var if0 =
      new NPTXSIf(
        zero(),
        new NPTXETrue(zero()),
        List.of(),
        List.of()
      );

    final var if1 =
      new NPTXSIf(
        zero(),
        new NPTXETrue(zero()),
        List.of(),
        List.of()
      );

    NPTXChecker.checkStatement(
      v2,
      new NPTXSIf(
        zero(),
        new NPTXETrue(zero()),
        List.of(if0),
        List.of(if1))
    );
  }

  @Property
  public void testCheckETrue(
    final @ForAll NPTXPlanVariables variables)
    throws Exception
  {
    assertEquals(
      TYPE_BOOLEAN,
      NPTXChecker.checkExpression(
        variables,
        new NPTXETrue(zero())
      )
    );
  }

  @Property
  public void testCheckEAnd(
    final @ForAll NPTXPlanVariables variables)
    throws Exception
  {
    assertEquals(
      TYPE_BOOLEAN,
      NPTXChecker.checkExpression(
        variables,
        new NPTXEAnd(zero(), new NPTXETrue(zero()), new NPTXETrue(zero()))
      )
    );
  }

  @Property
  public void testCheckEAndNotBoolean0(
    final @ForAll NPTXPlanVariables variables)
    throws Exception
  {
    final var ex =
      assertThrows(NPTXCheckerException.class, () -> {
        NPTXChecker.checkExpression(
          variables,
          new NPTXEAnd(zero(), new NPTXENumber(zero(), BigInteger.ONE), new NPTXETrue(zero()))
        );
      });

    assertEquals(TYPE_CHECK_EXPRESSION, ex.message());
  }

  @Property
  public void testCheckEAndNotBoolean1(
    final @ForAll NPTXPlanVariables variables)
    throws Exception
  {
    final var ex =
      assertThrows(NPTXCheckerException.class, () -> {
        NPTXChecker.checkExpression(
          variables,
          new NPTXEAnd(zero(), new NPTXETrue(zero()), new NPTXENumber(zero(), BigInteger.ONE))
        );
      });

    assertEquals(TYPE_CHECK_EXPRESSION, ex.message());
  }

  @Property
  public void testCheckEOr(
    final @ForAll NPTXPlanVariables variables)
    throws Exception
  {
    assertEquals(
      TYPE_BOOLEAN,
      NPTXChecker.checkExpression(
        variables,
        new NPTXEOr(zero(), new NPTXETrue(zero()), new NPTXETrue(zero()))
      )
    );
  }

  @Property
  public void testCheckEOrNotBoolean0(
    final @ForAll NPTXPlanVariables variables)
    throws Exception
  {
    final var ex =
      assertThrows(NPTXCheckerException.class, () -> {
        NPTXChecker.checkExpression(
          variables,
          new NPTXEOr(zero(), new NPTXENumber(zero(), BigInteger.ONE), new NPTXETrue(zero()))
        );
      });

    assertEquals(TYPE_CHECK_EXPRESSION, ex.message());
  }

  @Property
  public void testCheckEOrNotBoolean1(
    final @ForAll NPTXPlanVariables variables)
    throws Exception
  {
    final var ex =
      assertThrows(NPTXCheckerException.class, () -> {
        NPTXChecker.checkExpression(
          variables,
          new NPTXEOr(zero(), new NPTXETrue(zero()), new NPTXENumber(zero(), BigInteger.ONE))
        );
      });

    assertEquals(TYPE_CHECK_EXPRESSION, ex.message());
  }

  @Property
  public void testCheckENot(
    final @ForAll NPTXPlanVariables variables)
    throws Exception
  {
    assertEquals(
      TYPE_BOOLEAN,
      NPTXChecker.checkExpression(
        variables,
        new NPTXENot(zero(), new NPTXETrue(zero()))
      )
    );
  }

  @Property
  public void testCheckENotNotBoolean0(
    final @ForAll NPTXPlanVariables variables)
    throws Exception
  {
    final var ex =
      assertThrows(NPTXCheckerException.class, () -> {
        NPTXChecker.checkExpression(
          variables,
          new NPTXENot(zero(), new NPTXENumber(zero(), BigInteger.ONE))
        );
      });

    assertEquals(TYPE_CHECK_EXPRESSION, ex.message());
  }

  @Property
  public void testCheckEFalse(
    final @ForAll NPTXPlanVariables variables)
    throws Exception
  {
    assertEquals(
      TYPE_BOOLEAN,
      NPTXChecker.checkExpression(
        variables,
        new NPTXEFalse(zero())
      )
    );
  }

  @Property
  public void testCheckENumber(
    final @ForAll NPTXPlanVariables variables,
    final @ForAll BigInteger value)
    throws Exception
  {
    assertEquals(
      TYPE_NUMERIC,
      NPTXChecker.checkExpression(
        variables,
        new NPTXENumber(zero(), value)
      )
    );
  }

  @Property
  public void testCheckEString(
    final @ForAll NPTXPlanVariables variables,
    final @ForAll String value)
    throws Exception
  {
    assertEquals(
      TYPE_STRING,
      NPTXChecker.checkExpression(
        variables,
        new NPTXEString(zero(), value)
      )
    );
  }

  @Property
  public void testCheckEVariableBoolean(
    final @ForAll NPTXPlanVariables variables,
    final @ForAll RDottedName name)
    throws Exception
  {
    final var vr =
      new NPTXPlanVariableBoolean(name, true);
    final var vm = new HashMap<>(variables.variables());
    vm.put(vr.name(), vr);
    final var v2 = new NPTXPlanVariables(vm);

    assertEquals(
      TYPE_BOOLEAN,
      NPTXChecker.checkExpression(
        v2,
        new NPTXEVariableBoolean(zero(), name)
      )
    );
  }

  @Property
  public void testCheckEVariableBooleanMissing(
    final @ForAll NPTXPlanVariables variables,
    final @ForAll RDottedName name)
    throws Exception
  {
    final var vm = new HashMap<>(variables.variables());
    vm.remove(name);
    final var v2 = new NPTXPlanVariables(vm);

    final var ex =
      assertThrows(NPTXCheckerException.class, () -> {
        NPTXChecker.checkExpression(
          v2,
          new NPTXEVariableBoolean(zero(), name)
        );
      });

    assertEquals(TYPE_CHECK_UNDEFINED_VARIABLE, ex.message());
  }

  @Property
  public void testCheckEVariableBooleanWrongType(
    final @ForAll NPTXPlanVariables variables,
    final @ForAll RDottedName name)
    throws Exception
  {
    final var vr =
      new NPTXPlanVariableNumeric(name, Integer.valueOf(23));
    final var vm = new HashMap<>(variables.variables());
    vm.put(vr.name(), vr);
    final var v2 = new NPTXPlanVariables(vm);

    final var ex =
      assertThrows(NPTXCheckerException.class, () -> {
        NPTXChecker.checkExpression(
          v2,
          new NPTXEVariableBoolean(zero(), name)
        );
      });

    assertEquals(TYPE_CHECK_PLAN_VARIABLE, ex.message());
  }

  @Property
  public void testCheckEVariableNumber(
    final @ForAll NPTXPlanVariables variables,
    final @ForAll RDottedName name)
    throws Exception
  {
    final var vr =
      new NPTXPlanVariableNumeric(name, Integer.valueOf(23));
    final var vm = new HashMap<>(variables.variables());
    vm.put(vr.name(), vr);
    final var v2 = new NPTXPlanVariables(vm);

    assertEquals(
      TYPE_NUMERIC,
      NPTXChecker.checkExpression(
        v2,
        new NPTXEVariableNumber(zero(), name)
      )
    );
  }

  @Property
  public void testCheckEVariableNumericMissing(
    final @ForAll NPTXPlanVariables variables,
    final @ForAll RDottedName name)
    throws Exception
  {
    final var vm = new HashMap<>(variables.variables());
    vm.remove(name);
    final var v2 = new NPTXPlanVariables(vm);

    final var ex =
      assertThrows(NPTXCheckerException.class, () -> {
        NPTXChecker.checkExpression(
          v2,
          new NPTXEVariableNumber(zero(), name)
        );
      });

    assertEquals(TYPE_CHECK_UNDEFINED_VARIABLE, ex.message());
  }

  @Property
  public void testCheckEVariableNumericWrongType(
    final @ForAll NPTXPlanVariables variables,
    final @ForAll RDottedName name)
    throws Exception
  {
    final var vr =
      new NPTXPlanVariableBoolean(name, true);
    final var vm = new HashMap<>(variables.variables());
    vm.put(vr.name(), vr);
    final var v2 = new NPTXPlanVariables(vm);

    final var ex =
      assertThrows(NPTXCheckerException.class, () -> {
        NPTXChecker.checkExpression(
          v2,
          new NPTXEVariableNumber(zero(), name)
        );
      });

    assertEquals(TYPE_CHECK_PLAN_VARIABLE, ex.message());
  }

  @Property
  public void testCheckEVariableString(
    final @ForAll NPTXPlanVariables variables,
    final @ForAll RDottedName name)
    throws Exception
  {
    final var vr =
      new NPTXPlanVariableString(name, "3");
    final var vm = new HashMap<>(variables.variables());
    vm.put(vr.name(), vr);
    final var v2 = new NPTXPlanVariables(vm);

    assertEquals(
      TYPE_STRING,
      NPTXChecker.checkExpression(
        v2,
        new NPTXEVariableString(zero(), name)
      )
    );
  }

  @Property
  public void testCheckEVariableStringMissing(
    final @ForAll NPTXPlanVariables variables,
    final @ForAll RDottedName name)
    throws Exception
  {
    final var vm = new HashMap<>(variables.variables());
    vm.remove(name);
    final var v2 = new NPTXPlanVariables(vm);

    final var ex =
      assertThrows(NPTXCheckerException.class, () -> {
        NPTXChecker.checkExpression(
          v2,
          new NPTXEVariableString(zero(), name)
        );
      });

    assertEquals(TYPE_CHECK_UNDEFINED_VARIABLE, ex.message());
  }

  @Property
  public void testCheckEVariableStringWrongType(
    final @ForAll NPTXPlanVariables variables,
    final @ForAll RDottedName name)
    throws Exception
  {
    final var vr =
      new NPTXPlanVariableBoolean(name, true);
    final var vm = new HashMap<>(variables.variables());
    vm.put(vr.name(), vr);
    final var v2 = new NPTXPlanVariables(vm);

    final var ex =
      assertThrows(NPTXCheckerException.class, () -> {
        NPTXChecker.checkExpression(
          v2,
          new NPTXEVariableString(zero(), name)
        );
      });

    assertEquals(TYPE_CHECK_PLAN_VARIABLE, ex.message());
  }

  @Property
  public void testCheckEIsEqual(
    final @ForAll NPTXPlanVariables variables)
    throws Exception
  {
    assertEquals(
      TYPE_BOOLEAN,
      NPTXChecker.checkExpression(
        variables,
        new NPTXEIsEqual(
          zero(),
          new NPTXENumber(zero(), BigInteger.ONE),
          new NPTXENumber(zero(), BigInteger.ONE)
        )
      )
    );
  }

  @Property
  public void testCheckEIsEqualWrongType(
    final @ForAll NPTXPlanVariables variables)
    throws Exception
  {
    final var ex =
      assertThrows(NPTXCheckerException.class, () -> {
        NPTXChecker.checkExpression(
          variables,
          new NPTXEIsEqual(
            zero(),
            new NPTXENumber(zero(), BigInteger.ONE),
            new NPTXETrue(zero())
          )
        );
      });

    assertEquals(TYPE_CHECK_EXPRESSION, ex.message());
  }

  @Test
  public void testExample0()
    throws Exception
  {
    final var input =
      NPTXCheckingTest.class.getResourceAsStream(
        "/com/io7m/northpike/tests/toolexec-0.xml");

    final var parser =
      NPTXDescriptionParser.open(
        input,
        URI.create("urn:stdin"),
        NPPreserveLexical.DISCARD_LEXICAL_INFORMATION,
        parseStatus -> {

        });

    final var description =
      parser.execute();

    final var variables =
      new NPTXPlanVariables(
        Map.ofEntries(
          Map.entry(
            new RDottedName("com.io7m.northpike.scm.is-tagged"),
            new NPTXPlanVariableBoolean(
              new RDottedName("com.io7m.northpike.scm.is-tagged"),
              true
            )
          ),
          Map.entry(
            new RDottedName("com.io7m.northpike.scm.branch"),
            new NPTXPlanVariableString(
              new RDottedName("com.io7m.northpike.scm.branch"),
              "master"
            )
          )
        )
      );

    final var checked =
      NPTXChecker.checkDescription(variables, description);
  }

  @Test
  public void testExampleError0()
    throws Exception
  {
    final var input =
      NPTXCheckingTest.class.getResourceAsStream(
        "/com/io7m/northpike/tests/toolexec-0.xml");

    final var parser =
      NPTXDescriptionParser.open(
        input,
        URI.create("urn:stdin"),
        NPPreserveLexical.DISCARD_LEXICAL_INFORMATION,
        parseStatus -> {

        });

    final var description =
      parser.execute();

    final var variables =
      new NPTXPlanVariables(
        Map.ofEntries(
          Map.entry(
            new RDottedName("com.io7m.northpike.scm.branch"),
            new NPTXPlanVariableString(
              new RDottedName("com.io7m.northpike.scm.branch"),
              "master"
            )
          )
        )
      );

    assertThrows(NPTXCheckerException.class, () -> {
      NPTXChecker.checkDescription(variables, description);
    });
  }
}
