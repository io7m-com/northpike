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


package com.io7m.northpike.protocol.user.cb.internal;

import com.io7m.cedarbridge.runtime.api.CBSerializableType;
import com.io7m.northpike.model.comparisons.NPComparisonExactType;
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1ComparisonExact;

import java.util.Objects;

/**
 * Exact comparisons.
 *
 * @param <V> The type of model values
 * @param <W> The type of serialized values
 */

public final class NPUVComparisonsExact<V, W extends CBSerializableType>
  implements NPProtocolMessageValidatorType<
  NPComparisonExactType<V>,
  NPU1ComparisonExact<W>>
{
  private final NPProtocolMessageValidatorType<V, W> validator;

  /**
   * Exact comparisons.
   *
   * @param inValidator A validator for values
   */

  public NPUVComparisonsExact(
    final NPProtocolMessageValidatorType<V, W> inValidator)
  {
    this.validator =
      Objects.requireNonNull(inValidator, "validator");
  }

  @Override
  public NPU1ComparisonExact<W> convertToWire(
    final NPComparisonExactType<V> message)
    throws NPProtocolException
  {
    if (message instanceof NPComparisonExactType.Anything<V>) {
      return new NPU1ComparisonExact.Anything<>();
    }

    if (message instanceof final NPComparisonExactType.IsEqualTo<V> e) {
      return new NPU1ComparisonExact.IsEqualTo<>(
        this.validator.convertToWire(e.value())
      );
    }

    if (message instanceof final NPComparisonExactType.IsNotEqualTo<V> e) {
      return new NPU1ComparisonExact.IsNotEqualTo<>(
        this.validator.convertToWire(e.value())
      );
    }

    throw new IllegalStateException(
      "Unrecognized message: %s".formatted(message)
    );
  }

  @Override
  public NPComparisonExactType<V> convertFromWire(
    final NPU1ComparisonExact<W> message)
    throws NPProtocolException
  {
    if (message instanceof NPU1ComparisonExact.Anything<W>) {
      return new NPComparisonExactType.Anything<>();
    }

    if (message instanceof final NPU1ComparisonExact.IsEqualTo<W> e) {
      return new NPComparisonExactType.IsEqualTo<>(
        this.validator.convertFromWire(e.fieldValue())
      );
    }

    if (message instanceof final NPU1ComparisonExact.IsNotEqualTo<W> e) {
      return new NPComparisonExactType.IsNotEqualTo<>(
        this.validator.convertFromWire(e.fieldValue())
      );
    }

    throw new IllegalStateException(
      "Unrecognized message: %s".formatted(message)
    );
  }
}
