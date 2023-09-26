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


package com.io7m.northpike.plans.compiler;

import com.io7m.anethum.api.ParseSeverity;
import com.io7m.anethum.api.ParseStatusType;
import com.io7m.anethum.api.ParsingException;
import com.io7m.northpike.model.NPCompilationMessage;
import com.io7m.northpike.model.NPFormatName;
import com.io7m.northpike.model.plans.NPPlanException;
import com.io7m.northpike.plans.NPPlans;
import com.io7m.northpike.plans.compiler.NPPlanCompilationResultType.Success;

import java.io.ByteArrayInputStream;
import java.net.URI;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import static com.io7m.northpike.model.NPCompilationMessage.Kind.ERROR;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_FORMAT_UNSUPPORTED;
import static java.nio.charset.StandardCharsets.UTF_8;

/**
 * The default compiler factory.
 */

public final class NPPlanCompilers implements NPPlanCompilerFactoryType
{
  /**
   * The default compiler factory.
   */

  public NPPlanCompilers()
  {

  }

  @Override
  public NPPlanCompilerType create(
    final NPPlanCompilerConfiguration configuration)
  {
    return new NPPlanCompiler(configuration);
  }

  @Override
  public String description()
  {
    return "Plan compiler service.";
  }

  private static final class NPPlanCompiler implements NPPlanCompilerType
  {
    private final NPPlanCompilerConfiguration configuration;

    NPPlanCompiler(
      final NPPlanCompilerConfiguration inConfiguration)
    {
      this.configuration =
        Objects.requireNonNull(inConfiguration, "configuration");
    }

    @Override
    public NPPlanCompilationResultType execute(
      final NPFormatName format,
      final String text)
    {
      Objects.requireNonNull(format, "format");
      Objects.requireNonNull(text, "text");

      final var strings =
        this.configuration.strings();
      final var parsersAvailable =
        this.configuration.parsers();

      final var parsersSupportingFormat =
        parsersAvailable.stream()
          .filter(p -> p.formats().contains(format))
          .toList();

      if (parsersSupportingFormat.isEmpty()) {
        return new NPPlanCompilationResultType.Failure(
          List.of(
            new NPCompilationMessage(
              ERROR,
              0,
              0,
              strings.format(ERROR_FORMAT_UNSUPPORTED)
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

          return new Success(NPPlans.toPlan(parsed, strings));
        } catch (final ParsingException e) {
          messages.addAll(
            e.statusValues()
              .stream()
              .map(NPPlanCompilers::mapStatus)
              .toList()
          );
        } catch (final NPPlanException e) {
          messages.add(
            new NPCompilationMessage(
              ERROR,
              0,
              0,
              e.getMessage()
            )
          );
        }
      }

      return new NPPlanCompilationResultType.Failure(
        List.copyOf(messages)
      );
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
      case PARSE_ERROR -> ERROR;
      case PARSE_WARNING -> NPCompilationMessage.Kind.WARNING;
      case PARSE_INFO -> NPCompilationMessage.Kind.INFO;
    };
  }
}
