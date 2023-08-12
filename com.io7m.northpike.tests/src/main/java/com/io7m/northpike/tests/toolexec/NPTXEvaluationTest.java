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

import com.io7m.anethum.api.ParsingException;
import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.toolexec.NPTXPreserveLexical;
import com.io7m.northpike.toolexec.checker.NPTXChecker;
import com.io7m.northpike.toolexec.checker.NPTXCheckerException;
import com.io7m.northpike.toolexec.evaluator.NPTXEvaluator;
import com.io7m.northpike.toolexec.model.NPTXPlanVariableBoolean;
import com.io7m.northpike.toolexec.model.NPTXPlanVariableNumeric;
import com.io7m.northpike.toolexec.model.NPTXPlanVariableString;
import com.io7m.northpike.toolexec.model.NPTXPlanVariableStringSet;
import com.io7m.northpike.toolexec.model.NPTXPlanVariables;
import com.io7m.northpike.toolexec.parser.NPTXDescriptionParser;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.TestFactory;

import java.math.BigInteger;
import java.net.URI;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;

public final class NPTXEvaluationTest
{
  @TestFactory
  public Stream<DynamicTest> testExamples()
  {
    return IntStream.range(0, 14)
      .mapToObj(x -> {
        return DynamicTest.dynamicTest("Example" + x, () -> {
          final var vb =
            new NPTXPlanVariableBoolean(new RDottedName("vb"), true);
          final var vn =
            new NPTXPlanVariableNumeric(new RDottedName("vn"), BigInteger.ONE);
          final var vs =
            new NPTXPlanVariableString(new RDottedName("vs"), "x");
          final var vss =
            new NPTXPlanVariableStringSet(new RDottedName("vss"), Set.of("X"));

          final var variables =
            NPTXPlanVariables.ofList(List.of(vb, vn, vs, vss));

          checkOK("toolexec-eval-%d.xml".formatted(x), variables);
        });
      });
  }

  private static void checkOK(
    final String name,
    final NPTXPlanVariables variables)
    throws ParsingException, NPTXCheckerException
  {
    final var input =
      NPTXEvaluationTest.class.getResourceAsStream(
        "/com/io7m/northpike/tests/" + name);

    final var parser =
      NPTXDescriptionParser.open(
        input,
        URI.create("urn:stdin"),
        NPTXPreserveLexical.DISCARD_LEXICAL_INFORMATION,
        parseStatus -> {

        });

    final var description =
      parser.execute();
    final var checked =
      NPTXChecker.checkDescription(variables, description);
    final var evaluator =
      new NPTXEvaluator(
        Map.ofEntries(Map.entry("ENV0", "X")),
        checked
      );
    final var evaluated =
      evaluator.evaluate();

    assertEquals(
      List.of(
        "ok"
      ),
      evaluated.arguments()
    );
  }
}
