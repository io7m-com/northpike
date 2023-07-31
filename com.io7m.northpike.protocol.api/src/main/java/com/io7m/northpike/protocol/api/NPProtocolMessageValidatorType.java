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

package com.io7m.northpike.protocol.api;

/**
 * The type of validators that convert between core messages and "wire"
 * (versioned) messages.
 *
 * @param <T> The type of core messages
 * @param <R> The type of wire messages
 */

public interface NPProtocolMessageValidatorType<T, R>
{
  /**
   * Convert a core message to a wire message.
   *
   * @param message The core message
   *
   * @return The wire message
   *
   * @throws NPProtocolException On errors
   */

  R convertToWire(T message)
    throws NPProtocolException;

  /**
   * Convert a wire message to a core message.
   *
   * @param message The wire message
   *
   * @return The core message
   *
   * @throws NPProtocolException On errors
   */

  T convertFromWire(R message)
    throws NPProtocolException;
}
