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

package com.io7m.northpike.toolexec.checker;

import com.io7m.jlexing.core.LexicalPosition;
import com.io7m.jlexing.core.LexicalType;
import com.io7m.northpike.strings.NPStringConstantType;
import com.io7m.northpike.toolexec.model.NPTXExecutableType;

import java.net.URI;
import java.util.Objects;

/**
 * An exception raised during type checking.
 */

public final class NPTXCheckerException
  extends Exception
  implements LexicalType<URI>
{
  private final NPTXExecutableType element;
  private final NPTXType expectedType;
  private final NPTXType receivedType;
  private final NPStringConstantType message;

  /**
   * @return The ill-typed element
   */

  public NPTXExecutableType element()
  {
    return this.element;
  }

  /**
   * @return The expected type
   */

  public NPTXType expectedType()
  {
    return this.expectedType;
  }

  /**
   * @return The received type
   */

  public NPTXType receivedType()
  {
    return this.receivedType;
  }

  /**
   * @return The error message
   */

  public NPStringConstantType message()
  {
    return this.message;
  }

  /**
   * Construct an exception.
   *
   * @param inMessage      The message
   * @param inElement      The element
   * @param inExpectedType The expected type
   * @param inReceivedType The received type
   */

  public NPTXCheckerException(
    final NPStringConstantType inMessage,
    final NPTXExecutableType inElement,
    final NPTXType inExpectedType,
    final NPTXType inReceivedType)
  {
    this.message =
      Objects.requireNonNull(inMessage, "inMessage");
    this.element =
      Objects.requireNonNull(inElement, "inElement");
    this.expectedType =
      Objects.requireNonNull(inExpectedType, "inExpectedType");
    this.receivedType =
      Objects.requireNonNull(inReceivedType, "inReceivedType");
  }

  @Override
  public LexicalPosition<URI> lexical()
  {
    return this.element.lexical();
  }
}
