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


package com.io7m.northpike.tests.toolexecj;

import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.toolexecj.runner.NPTJException;
import com.io7m.northpike.toolexecj.runner.NPTJRunnerServiceType;
import com.io7m.northpike.toolexecj.runner.NPTJRunners;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.TestFactory;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.NoSuchFileException;
import java.util.Arrays;
import java.util.Locale;
import java.util.stream.Stream;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorCompilationFailed;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorToolExecutionFailed;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

public final class NPTJRunnerTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPTJRunnerTest.class);

  private NPTJRunnerServiceType runners;

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
    this.runners = NPTJRunners.create(NPStrings.create(Locale.ROOT));
  }

  record FailureCase(
    String name,
    NPErrorCode errorCode)
  {

  }

  @TestFactory
  public Stream<DynamicTest> testCompileFailures()
    throws Exception
  {
    return Stream.of(
      new FailureCase("TEJError0", errorCompilationFailed()),
      new FailureCase("TEJError1", errorToolExecutionFailed()),
      new FailureCase("TEJError2", errorToolExecutionFailed()),
      new FailureCase("TEJError3", errorToolExecutionFailed()),
      new FailureCase("TEJError4", errorToolExecutionFailed())
    ).map(failureCase -> {
      return DynamicTest.dynamicTest("testCompileFailure_" + failureCase.name, () -> {
        this.fail(failureCase);
      });
    });
  }

  @Test
  public void testCompileCorruptBytecode()
    throws Exception
  {
    final var runner =
      this.runners.create(
        "TEJError1",
        text("TEJError1.java"),
        NPTJRunnerTest::corrupt
      );

    final var ex =
      assertThrows(NPTJException.class, runner::execute);

    LOG.error("", ex);
    for (final var e : ex.errors()) {
      LOG.error("{}", e);
    }
  }

  private void fail(
    final FailureCase failureCase)
    throws IOException
  {
    final var runner =
      this.runners.create(
        failureCase.name,
        text(failureCase.name + ".java")
      );

    final var ex =
      assertThrows(NPTJException.class, runner::execute);

    LOG.error("", ex);
    for (final var e : ex.errors()) {
      LOG.error("{}", e);
    }

    assertEquals(failureCase.errorCode, ex.errorCode());
  }

  private static byte[] corrupt(
    final byte[] bytes)
  {
    final var copy = Arrays.copyOf(bytes, bytes.length);
    for (int index = 0; index < copy.length; ++index) {
      copy[index] = (byte) ((int) copy[index] ^ 0x23);
    }
    return copy;
  }
}
