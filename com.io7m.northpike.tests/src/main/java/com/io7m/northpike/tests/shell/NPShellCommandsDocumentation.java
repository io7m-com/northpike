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


package com.io7m.northpike.tests.shell;

import com.io7m.northpike.shell.NPShellConfiguration;
import com.io7m.northpike.shell.NPShells;
import com.io7m.northpike.shell.commons.NPShellValueConverters;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.user_client.NPUserClients;
import com.io7m.quarrel.core.QCommandOrGroupType;
import com.io7m.quarrel.core.QCommandParserConfiguration;
import com.io7m.quarrel.core.QCommandParsers;
import com.io7m.quarrel.ext.xstructural.QCommandXS;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Optional;
import java.util.TreeMap;
import java.util.stream.Collectors;

public final class NPShellCommandsDocumentation
{
  private NPShellCommandsDocumentation()
  {

  }

  public static void main(
    final String[] args)
    throws Exception
  {
    final var shells =
      new NPShells();
    final var tempFile =
      Files.createTempFile("northpike-", ".txt");

    Files.deleteIfExists(tempFile);

    final var configuration =
      new NPShellConfiguration(
        Locale.ROOT,
        new NPUserClients(),
        NPStrings.create(Locale.ROOT),
        Optional.empty(),
        1_000_000
      );

    final var parsers =
      new QCommandParsers();
    final var xs =
      new QCommandXS("xs", true);

    final var converters =
      NPShellValueConverters.get();

    final var parserConfig =
      new QCommandParserConfiguration(
        converters,
        QCommandParsers.emptyResources()
      );

    try (var shell = shells.create(configuration)) {
      final var commands = shell.commands();

      final var byName =
        new TreeMap<String, QCommandOrGroupType>(
          commands.stream()
            .map(c -> Map.entry(c.metadata().name(), c))
            .collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue))
        );

      for (final var command : commands) {
        try {
          final var name =
            command.metadata().name();
          final var parser =
            parsers.create(parserConfig);

          {
            final var textWriter =
              new StringWriter();
            final var writer =
              new PrintWriter(textWriter);

            final var paramsInclude =
              "scmd-%s-parameters.xml".formatted(name);

            final var context =
              parser.execute(
                byName,
                writer,
                xs,
                List.of(
                  "--type",
                  "main",
                  "--parameters-include",
                  paramsInclude,
                  name
                )
              );

            context.execute();
            writer.println();
            writer.flush();

            final var mainFile =
              Paths.get("/shared-tmp/scmd-%s.xml".formatted(name));

            Files.writeString(
              mainFile,
              textWriter.toString(),
              StandardCharsets.UTF_8
            );
          }

          {
            final var textWriter =
              new StringWriter();
            final var writer =
              new PrintWriter(textWriter);

            final var context =
              parser.execute(
                byName,
                writer,
                xs,
                List.of("--type", "parameters", name)
              );

            context.execute();
            writer.println();
            writer.flush();

            final var paramsFile =
              Paths.get("/shared-tmp/scmd-%s-parameters.xml".formatted(name));

            Files.writeString(
              paramsFile,
              textWriter.toString(),
              StandardCharsets.UTF_8
            );
          }

        } catch (final Exception e) {
          e.printStackTrace();
        }
      }

      for (final var command : commands) {
        final var name = command.metadata().name();
        System.out.printf("<xi:include href=\"scmd-%s.xml\"/>%n", name);
      }
    }
  }
}
