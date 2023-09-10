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


package com.io7m.northpike.toolexec;

import com.io7m.anethum.api.ParseSeverity;
import com.io7m.anethum.api.ParseStatusType;
import com.io7m.anethum.api.ParsingException;
import com.io7m.northpike.model.NPCompilationMessage;
import com.io7m.northpike.model.NPFormatName;
import com.io7m.northpike.toolexec.checker.NPTXChecker;
import com.io7m.northpike.toolexec.checker.NPTXCheckerException;
import com.io7m.northpike.toolexec.model.NPTXDescription;
import com.io7m.northpike.toolexec.model.NPTXPlanVariables;

import java.io.ByteArrayInputStream;
import java.net.URI;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import static com.io7m.northpike.strings.NPStringConstants.ERROR_FORMAT_UNSUPPORTED;
import static java.nio.charset.StandardCharsets.UTF_8;

/**
 * The default compiler factory.
 */

public final class NPTXCompilers implements NPTXCompilerFactoryType
{
  /**
   * The default compiler factory.
   */

  public NPTXCompilers()
  {

  }

  @Override
  public NPTXCompilerType create(
    final NPTXCompilerConfiguration configuration)
  {
    return new NPTXCompiler(configuration);
  }

  @Override
  public String description()
  {
    return "Tool execution compiler service.";
  }

  private static final class NPTXCompiler implements NPTXCompilerType
  {
    private final NPTXCompilerConfiguration configuration;

    NPTXCompiler(
      final NPTXCompilerConfiguration inConfiguration)
    {
      this.configuration =
        Objects.requireNonNull(inConfiguration, "configuration");
    }

    @Override
    public NPTXCompilationResultType execute(
      final NPTXPlanVariables variables,
      final NPFormatName format,
      final String text)
    {
      Objects.requireNonNull(variables, "variables");
      Objects.requireNonNull(format, "format");
      Objects.requireNonNull(text, "text");

      final var parsersAvailable =
        this.configuration.parsers();

      final var parsersSupportingFormat =
        parsersAvailable.stream()
          .filter(p -> p.formats().contains(format))
          .toList();

      if (parsersSupportingFormat.isEmpty()) {
        return new NPTXCompilationResultType.Failure(
          List.of(
            new NPCompilationMessage(
              NPCompilationMessage.Kind.ERROR,
              0,
              0,
              this.configuration.strings().format(ERROR_FORMAT_UNSUPPORTED)
            )
          )
        );
      }

      final var textBytes =
        text.getBytes(UTF_8);
      final var messages =
        new ArrayList<NPCompilationMessage>();

      for (final var parsers : parsersSupportingFormat) {
        try {
          final var parsed =
            parsers.parse(
              URI.create("urn:stdin"),
              new ByteArrayInputStream(textBytes)
            );

          return this.typeCheck(variables, parsed);
        } catch (final ParsingException e) {
          messages.addAll(
            e.statusValues()
              .stream()
              .map(NPTXCompilers::mapStatus)
              .toList()
          );
        }
      }

      return new NPTXCompilationResultType.Failure(
        List.copyOf(messages)
      );
    }

    private NPTXCompilationResultType typeCheck(
      final NPTXPlanVariables variables,
      final NPTXDescription parsed)
    {
      try {
        final var result =
          NPTXChecker.checkDescription(variables, parsed);

        return new NPTXCompilationResultType.Success(result);
      } catch (final NPTXCheckerException e) {
        final var messages = new ArrayList<NPCompilationMessage>();

        messages.add(
          new NPCompilationMessage(
            NPCompilationMessage.Kind.ERROR,
            e.lexical().line(),
            e.lexical().column(),
            this.configuration.strings().format(e.message())
          )
        );

        for (final var x : e.getSuppressed()) {
          if (x instanceof final NPTXCheckerException ex) {
            messages.add(
              new NPCompilationMessage(
                NPCompilationMessage.Kind.ERROR,
                ex.lexical().line(),
                ex.lexical().column(),
                this.configuration.strings().format(ex.message())
              )
            );
          }
        }

        return new NPTXCompilationResultType.Failure(List.copyOf(messages));
      }
    }
  }

  private static NPCompilationMessage mapStatus(
    final ParseStatusType status)
  {
    return new NPCompilationMessage(
      mapKind(status.severity()),
      status.lexical().line(),
      status.lexical().column(),
      status.message()
    );
  }

  private static NPCompilationMessage.Kind mapKind(
    final ParseSeverity severity)
  {
    return switch (severity) {
      case PARSE_ERROR -> NPCompilationMessage.Kind.ERROR;
      case PARSE_WARNING -> NPCompilationMessage.Kind.WARNING;
      case PARSE_INFO -> NPCompilationMessage.Kind.INFO;
    };
  }
}
