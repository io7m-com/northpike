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


package com.io7m.northpike.agent.configuration.v1;

import com.io7m.anethum.api.ParseSeverity;
import com.io7m.anethum.api.ParseStatus;
import com.io7m.anethum.api.ParsingException;
import com.io7m.blackthorne.core.BTException;
import com.io7m.blackthorne.core.BTParseError;
import com.io7m.blackthorne.core.BTPreserveLexical;
import com.io7m.blackthorne.jxe.BlackthorneJXE;
import com.io7m.northpike.agent.api.NPAgentHostConfiguration;
import com.io7m.northpike.agent.configuration.NPACParserType;
import com.io7m.northpike.agent.configuration.NPACPreserveLexical;
import com.io7m.northpike.agent.configuration.NPACSchemas;

import java.io.IOException;
import java.io.InputStream;
import java.net.URI;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.function.Consumer;

import static com.io7m.northpike.agent.configuration.NPACPreserveLexical.PRESERVE_LEXICAL_INFORMATION;

/**
 * A configuration file parser.
 */

public final class NPAC1FileParser implements NPACParserType
{
  private final URI source;
  private final InputStream stream;
  private final Consumer<ParseStatus> statusConsumer;
  private final BTPreserveLexical preserveLexical;

  /**
   * A configuration file parser.
   *
   * @param inPreserve       Whether to preserve lexical information
   * @param inSource         The source
   * @param inStream         The input stream
   * @param inStatusConsumer A status consumer
   */

  public NPAC1FileParser(
    final NPACPreserveLexical inPreserve,
    final URI inSource,
    final InputStream inStream,
    final Consumer<ParseStatus> inStatusConsumer)
  {
    this.preserveLexical =
      switch (Objects.requireNonNullElse(
        inPreserve,
        PRESERVE_LEXICAL_INFORMATION)) {
        case PRESERVE_LEXICAL_INFORMATION ->
          BTPreserveLexical.PRESERVE_LEXICAL_INFORMATION;
        case DISCARD_LEXICAL_INFORMATION ->
          BTPreserveLexical.DISCARD_LEXICAL_INFORMATION;
      };

    this.source =
      Objects.requireNonNull(inSource, "source");
    this.stream =
      Objects.requireNonNull(inStream, "stream");
    this.statusConsumer =
      Objects.requireNonNull(inStatusConsumer, "statusConsumer");
  }

  @Override
  public NPAgentHostConfiguration execute()
    throws ParsingException
  {
    try {
      return BlackthorneJXE.parse(
        this.source,
        this.stream,
        Map.ofEntries(
          Map.entry(
            NPACv1.element("Configuration"),
            NPAC1File::new
          )
        ),
        NPACSchemas.schemas(),
        this.preserveLexical
      );
    } catch (final BTException e) {
      final var statuses =
        e.errors()
          .stream()
          .map(NPAC1FileParser::mapParseError)
          .toList();

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
}
