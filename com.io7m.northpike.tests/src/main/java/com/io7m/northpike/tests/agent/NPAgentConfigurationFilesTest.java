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


package com.io7m.northpike.tests.agent;

import com.io7m.anethum.api.ParseStatus;
import com.io7m.anethum.api.ParsingException;
import com.io7m.northpike.agent.api.NPAgentConfiguration;
import com.io7m.northpike.agent.configuration.NPAgentConfigurationFiles;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.tests.scm_repository.NPSCMRepositoriesJGitTest;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

public final class NPAgentConfigurationFilesTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgentConfigurationFilesTest.class);

  @Test
  public void testParseError0(
    final @TempDir Path directory)
    throws Exception
  {
    final var file =
      directory.resolve("config.xml");

    copyOut("agent-config-error-0.xml", file);
    expectFailure(file);
  }

  @Test
  public void testParseError1(
    final @TempDir Path directory)
    throws Exception
  {
    final var file =
      directory.resolve("config.xml");

    copyOut("agent-config-error-1.xml", file);
    expectFailure(file);
  }

  @Test
  public void testParseError2(
    final @TempDir Path directory)
    throws Exception
  {
    final var file =
      directory.resolve("config.xml");

    copyOut("agent-config-error-2.xml", file);
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
    assertEquals(
      "example.com",
      configuration.remoteAddress().getHostName()
    );
    assertEquals(
      20048,
      configuration.remotePort()
    );
    assertEquals(
      "34139c57436e8451905273641fe64a2502fe4dbc5d8f9e0598105fc55384e6ef",
      configuration.accessKey().format()
    );
    assertTrue(configuration.useTLS());
    assertEquals(
      25600000,
      configuration.messageSizeLimit()
    );
  }

  private static NPAgentConfiguration expectSuccess(
    final Path file)
    throws Exception
  {
    try (var files =
           NPAgentConfigurationFiles.open(
             NPStrings.create(Locale.ROOT),
             file,
             NPAgentConfigurationFilesTest::onError)) {
      return files.execute();
    }
  }

  private static void expectFailure(
    final Path file)
    throws Exception
  {
    try (var files =
           NPAgentConfigurationFiles.open(
      NPStrings.create(Locale.ROOT),
      file,
      NPAgentConfigurationFilesTest::onError)) {
      assertThrows(ParsingException.class, files::execute);
    }
  }

  private static void onError(
    final ParseStatus parseStatus)
  {
    LOG.debug("{}", parseStatus);
  }

  private static void copyOut(
    final String name,
    final Path output)
    throws IOException
  {
    final var resourcePath =
      "/com/io7m/northpike/tests/%s".formatted(name);

    try (var input =
           NPSCMRepositoriesJGitTest.class.getResourceAsStream(resourcePath)) {
      if (input == null) {
        throw new FileNotFoundException(resourcePath);
      }
      Files.copy(input, output, StandardCopyOption.REPLACE_EXISTING);
    }
  }
}
