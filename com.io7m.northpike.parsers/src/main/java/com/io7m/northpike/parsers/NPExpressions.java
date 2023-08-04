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


package com.io7m.northpike.parsers;

import com.io7m.jeucreader.UnicodeCharacterReader;
import com.io7m.jsx.SExpressionType;
import com.io7m.jsx.api.lexer.JSXLexerComment;
import com.io7m.jsx.api.lexer.JSXLexerConfiguration;
import com.io7m.jsx.api.parser.JSXParserConfiguration;
import com.io7m.jsx.api.parser.JSXParserException;
import com.io7m.jsx.api.parser.JSXParserType;
import com.io7m.jsx.api.serializer.JSXSerializerType;
import com.io7m.jsx.lexer.JSXLexer;
import com.io7m.jsx.parser.JSXParser;
import com.io7m.jsx.serializer.JSXSerializerTrivial;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.strings.NPStringConstantType;
import com.io7m.northpike.strings.NPStrings;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.StringReader;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;

import static com.io7m.northpike.strings.NPStringConstants.ERROR_PARSE;
import static com.io7m.northpike.strings.NPStringConstants.OFFSET;
import static java.nio.charset.StandardCharsets.UTF_8;

/**
 * The base type of expression parsers.
 */

public abstract class NPExpressions
{
  private static final JSXLexerConfiguration LEXER_CONFIG =
    new JSXLexerConfiguration(
      true,
      true,
      Optional.empty(),
      EnumSet.of(JSXLexerComment.COMMENT_HASH),
      1
    );

  private static final JSXParserConfiguration PARSER_CONFIGURATION =
    new JSXParserConfiguration(true);

  private final NPStrings strings;

  protected NPExpressions(
    final NPStrings inStrings)
  {
    this.strings = Objects.requireNonNull(inStrings, "strings");
  }

  private static JSXParserType createParser(
    final String text)
  {
    final var reader =
      UnicodeCharacterReader.newReader(new StringReader(text));
    final var lexer =
      JSXLexer.newLexer(LEXER_CONFIG, reader);

    return JSXParser.newParser(PARSER_CONFIGURATION, lexer);
  }

  private static JSXSerializerType createSerializer()
  {
    return JSXSerializerTrivial.newSerializer();
  }

  /**
   * Serialize an expression to a string.
   *
   * @param expression The expression
   *
   * @return The serialized expression
   *
   * @throws NPException On errors
   */

  public static String serialize(
    final SExpressionType expression)
    throws NPException
  {
    try {
      try (var byteOut = new ByteArrayOutputStream()) {
        final var serializer = createSerializer();
        serializer.serialize(expression, byteOut);
        return byteOut.toString(UTF_8);
      }
    } catch (final IOException e) {
      throw new NPException(
        e.getMessage(),
        e,
        NPStandardErrorCodes.errorIo(),
        Map.of(),
        Optional.empty()
      );
    }
  }

  /**
   * Parse text as an s-expression.
   *
   * @param text The text
   *
   * @return The parsed expression
   *
   * @throws NPException On errors
   */

  public static SExpressionType parse(
    final String text)
    throws NPException
  {
    try {
      final var parser = createParser(text);
      return parser.parseExpression();
    } catch (final JSXParserException e) {
      throw new NPException(
        e.getMessage(),
        e,
        NPStandardErrorCodes.errorParse(),
        Map.of(),
        Optional.empty()
      );
    } catch (final IOException e) {
      throw new NPException(
        e.getMessage(),
        e,
        NPStandardErrorCodes.errorIo(),
        Map.of(),
        Optional.empty()
      );
    }
  }

  protected abstract Map<NPStringConstantType, NPStringConstantType> syntax();

  protected final NPException createParseError(
    final SExpressionType expression)
  {
    final var m = new HashMap<String, String>();
    for (final var entry : this.syntax().entrySet()) {
      m.put(
        this.strings.format(entry.getKey()),
        this.strings.format(entry.getValue())
      );
    }
    m.put(
      this.strings.format(OFFSET),
      Integer.toString(expression.lexical().column())
    );

    return new NPException(
      this.strings.format(ERROR_PARSE),
      NPStandardErrorCodes.errorParse(),
      m,
      Optional.empty()
    );
  }

  protected final NPException createParseError(
    final SExpressionType expression,
    final Exception e)
  {
    final var m = new HashMap<String, String>();
    for (final var entry : this.syntax().entrySet()) {
      m.put(
        this.strings.format(entry.getKey()),
        this.strings.format(entry.getValue())
      );
    }
    m.put(
      this.strings.format(OFFSET),
      Integer.toString(expression.lexical().column())
    );

    return new NPException(
      e.getMessage(),
      e,
      NPStandardErrorCodes.errorParse(),
      m,
      Optional.empty()
    );
  }
}
