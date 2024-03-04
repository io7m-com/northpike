/*
 * Copyright © 2024 Mark Raynsford <code@io7m.com> https://www.io7m.com
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


package com.io7m.northpike.tests.toolexec.js;

import com.io7m.northpike.toolexec.api.NPTEvaluationLanguageProviderType;
import com.io7m.northpike.toolexec.api.NPTException;
import com.io7m.northpike.toolexec.js.NPTJSLanguageProvider;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.TestFactory;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.NoSuchFileException;
import java.util.List;
import java.util.Map;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

public final class NPTJRunnerTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPTJRunnerTest.class);

  private NPTEvaluationLanguageProviderType runners;

  private static String text(
    final String name)
    throws IOException
  {
    final var path =
      "/com/io7m/northpike/tests/%s".formatted(name);
    final var url =
      NPTJRunnerTest.class.getResource(path);

    if (url == null) {
      throw new NoSuchFileException(path);
    }

    try (var stream = url.openStream()) {
      return new String(stream.readAllBytes(), StandardCharsets.UTF_8);
    }
  }

  @BeforeEach
  public void setup()
    throws IOException
  {
    this.runners = new NPTJSLanguageProvider();
  }

  @TestFactory
  public Stream<DynamicTest> testCompileFailures()
    throws Exception
  {
    return Stream.of(
      "ToolExecJ0",
      "ToolExecJ1",
      "ToolExecJ2"
    ).map(name -> {
      return DynamicTest.dynamicTest("testCompileFailure_" + name, () -> {
        this.fail(name);
      });
    });
  }

  @Test
  public void testSuccess0()
    throws NPTException
  {
    final var runner =
      this.runners.create(
        Map.ofEntries(
          Map.entry("X", "1"),
          Map.entry("Y", "2"),
          Map.entry("Z", "3")
        ),
"""
execution.environmentRemove("Y");
"""
      );

    final var result = runner.execute();
    assertEquals(List.of(), result.arguments());
    assertEquals(Map.ofEntries(
      Map.entry("X", "1"),
      Map.entry("Z", "3")
    ), result.environment());
  }

  @Test
  public void testSuccess1()
    throws NPTException
  {
    final var runner =
      this.runners.create(
        Map.ofEntries(
          Map.entry("X", "1"),
          Map.entry("Y", "2"),
          Map.entry("Z", "3")
        ),
        """
        execution.environmentClear();
        """
      );

    final var result = runner.execute();
    assertEquals(List.of(), result.arguments());
    assertEquals(Map.of(), result.environment());
  }

  @Test
  public void testSuccess2()
    throws NPTException
  {
    final var runner =
      this.runners.create(
        Map.ofEntries(
          Map.entry("X", "1"),
          Map.entry("Z", "3")
        ),
        """
        execution.environmentPut("Y", "2");
        """
      );

    final var result = runner.execute();
    assertEquals(List.of(), result.arguments());
    assertEquals(Map.ofEntries(
      Map.entry("X", "1"),
      Map.entry("Y", "2"),
      Map.entry("Z", "3")
    ), result.environment());
  }

  @Test
  public void testSuccess3()
    throws NPTException
  {
    final var runner =
      this.runners.create(
        Map.of(),
        """
        execution.argumentAdd("A");
        execution.argumentAdd("B");
        execution.argumentAdd("C");
        """
      );

    final var result = runner.execute();
    assertEquals(List.of("A", "B", "C"), result.arguments());
    assertEquals(Map.of(), result.environment());
  }

  @Test
  public void testSuccess4()
    throws NPTException
  {
    final var runner =
      this.runners.create(
        Map.of(),
        """
console.log("HELLO!");
        """
      );

    final var result = runner.execute();
    assertEquals(List.of(), result.arguments());
    assertTrue(result.outputMessages().stream().anyMatch(s -> s.contains("HELLO!")));
    assertEquals(Map.of(), result.environment());
  }

  private void fail(
    final String name)
    throws IOException
  {
    final var runner =
      this.runners.create(
        Map.of(),
        text(name + ".js")
      );

    final var ex =
      assertThrows(NPTException.class, runner::execute);

    LOG.error("", ex);
    for (final var e : ex.errors()) {
      LOG.error("{}", e);
    }
  }
}
