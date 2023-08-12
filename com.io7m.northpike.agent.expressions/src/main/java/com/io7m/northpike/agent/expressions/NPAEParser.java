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


package com.io7m.northpike.agent.expressions;

import com.io7m.anethum.api.ParseSeverity;
import com.io7m.anethum.api.ParseStatus;
import com.io7m.anethum.api.ParsingException;
import com.io7m.blackthorne.core.BTElementHandlerConstructorType;
import com.io7m.blackthorne.core.BTException;
import com.io7m.blackthorne.core.BTParseError;
import com.io7m.blackthorne.core.BTPreserveLexical;
import com.io7m.blackthorne.core.BTQualifiedName;
import com.io7m.blackthorne.jxe.BlackthorneJXE;
import com.io7m.northpike.agent.expressions.v1.NAE1Expressions;
import com.io7m.northpike.model.NPAgentLabelMatchType;

import java.io.Closeable;
import java.io.IOException;
import java.io.InputStream;
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.function.Consumer;
import java.util.stream.Collectors;

/**
 * A parser of tool executions.
 */

public final class NPAEParser implements Closeable
{
  private final URI source;
  private final InputStream stream;
  private final Consumer<ParseStatus> statusConsumer;
  private final BTPreserveLexical preserveLexical;

  /**
   * A parser of tool executions.
   *
   * @param inSource         The source
   * @param inStream         The stream
   * @param inStatusConsumer A status consumer
   * @param lexical          Whether to preserve lexical information
   */

  private NPAEParser(
    final URI inSource,
    final InputStream inStream,
    final Consumer<ParseStatus> inStatusConsumer,
    final NPAEPreserveLexical lexical)
  {
    this.source =
      Objects.requireNonNull(inSource, "source");
    this.stream =
      Objects.requireNonNull(inStream, "stream");
    this.statusConsumer =
      Objects.requireNonNull(inStatusConsumer, "statusConsumer");

    this.preserveLexical =
      switch (lexical) {
        case DISCARD_LEXICAL_INFORMATION ->
          BTPreserveLexical.DISCARD_LEXICAL_INFORMATION;
        case PRESERVE_LEXICAL_INFORMATION ->
          BTPreserveLexical.PRESERVE_LEXICAL_INFORMATION;
      };
  }

  private static ParseStatus mapParseError(
    final BTParseError error)
  {
    return ParseStatus.builder("parse-error", error.message())
      .withSeverity(mapSeverity(error.severity()))
      .withLexical(error.lexical())
      .build();
  }

  private static ParseSeverity mapSeverity(
    final BTParseError.Severity severity)
  {
    return switch (severity) {
      case ERROR -> ParseSeverity.PARSE_ERROR;
      case WARNING -> ParseSeverity.PARSE_WARNING;
    };
  }

  /**
   * Open the given tool execution file.
   *
   * @param file           The file
   * @param statusConsumer A consumer of error messages
   *
   * @return A parser
   *
   * @throws IOException On errors
   */

  public static NPAEParser open(
    final Path file,
    final Consumer<ParseStatus> statusConsumer)
    throws IOException
  {
    return open(
      Files.newInputStream(file),
      file.toUri(),
      NPAEPreserveLexical.PRESERVE_LEXICAL_INFORMATION,
      statusConsumer
    );
  }

  /**
   * Open the given tool execution file.
   *
   * @param statusConsumer A consumer of error messages
   * @param uri            The URI
   * @param inputStream    The input stream
   * @param lexical        Whether to preserve lexical information
   *
   * @return A parser
   */

  public static NPAEParser open(
    final InputStream inputStream,
    final URI uri,
    final NPAEPreserveLexical lexical,
    final Consumer<ParseStatus> statusConsumer)
  {
    return new NPAEParser(
      uri,
      inputStream,
      statusConsumer,
      lexical
    );
  }

  /**
   * Execute the parser.
   *
   * @return A configuration
   *
   * @throws ParsingException On errors
   */

  public NPAgentLabelMatchType execute()
    throws ParsingException
  {
    try {
      final Map<
        BTQualifiedName,
        BTElementHandlerConstructorType<?, NPAgentLabelMatchType>> roots =
        new HashMap<>();

      for (final var entry : NAE1Expressions.expressions().entrySet()) {
        roots.put(
          entry.getKey(),
          (BTElementHandlerConstructorType<?, NPAgentLabelMatchType>) entry.getValue()
        );
      }

      final NPAgentLabelMatchType configuration =
        BlackthorneJXE.parse(
          this.source,
          this.stream,
          roots,
          NAESchemas.labelExpressions(),
          this.preserveLexical
        );

      return configuration;
    } catch (final BTException e) {
      final var statuses =
        e.errors()
          .stream()
          .map(NPAEParser::mapParseError)
          .collect(Collectors.toList());

      for (final var status : statuses) {
        this.statusConsumer.accept(status);
      }

      throw new ParsingException(e.getMessage(), List.copyOf(statuses));
    }
  }

  @Override
  public void close()
    throws IOException
  {
    this.stream.close();
  }
}
