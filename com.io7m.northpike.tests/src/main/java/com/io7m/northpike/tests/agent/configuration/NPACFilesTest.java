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


package com.io7m.northpike.tests.agent.configuration;

import com.io7m.anethum.api.ParsingException;
import com.io7m.anethum.slf4j.ParseStatusLogging;
import com.io7m.northpike.agent.api.NPAgentHostConfiguration;
import com.io7m.northpike.agent.configuration.NPACFiles;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;

import static org.junit.jupiter.api.Assertions.assertThrows;

public final class NPACFilesTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPACFilesTest.class);

  @Test
  public void testParseError0(
    final @TempDir Path directory)
    throws Exception
  {
    final var file =
      directory.resolve("config.xml");

    copyOut("server-config-error-0.xml", file);
    expectFailure(file);
  }

  @Test
  public void testParseOk0(
    final @TempDir Path directory)
    throws Exception
  {
    final var file =
      directory.resolve("config.xml");

    copyOut("agent-config-0.xml", file);
    final var configuration = expectSuccess(file);
  }

  private static NPAgentHostConfiguration expectSuccess(
    final Path file)
    throws Exception
  {
    final var files = new NPACFiles();
    try (var parser = files.createParser(
      file,
      s -> ParseStatusLogging.logWithAll(LOG, s))) {
      return parser.execute();
    }
  }

  private static void expectFailure(
    final Path file)
    throws Exception
  {
    final var files = new NPACFiles();
    try (var parser = files.createParser(
      file,
      s -> ParseStatusLogging.logWithAll(LOG, s))) {
      assertThrows(ParsingException.class, parser::execute);
    }
  }

  private static void copyOut(
    final String name,
    final Path output)
    throws IOException
  {
    final var resourcePath =
      "/com/io7m/northpike/tests/%s".formatted(name);

    try (var input =
           NPACFilesTest.class.getResourceAsStream(resourcePath)) {
      if (input == null) {
        throw new FileNotFoundException(resourcePath);
      }
      Files.copy(input, output, StandardCopyOption.REPLACE_EXISTING);
    }
  }
}
