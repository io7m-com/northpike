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
import com.io7m.northpike.model.comparisons.NPComparisonFuzzyType;
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1ComparisonFuzzy;

import java.util.Objects;

/**
 * Fuzzy comparisons.
 *
 * @param <V> The type of model values
 * @param <W> The type of serialized values
 */

public final class NPUVComparisonsFuzzy<V, W extends CBSerializableType>
  implements NPProtocolMessageValidatorType<
  NPComparisonFuzzyType<V>,
  NPU1ComparisonFuzzy<W>>
{
  private final NPProtocolMessageValidatorType<V, W> validator;

  /**
   * Fuzzy comparisons.
   *
   * @param inValidator A validator for values
   */

  public NPUVComparisonsFuzzy(
    final NPProtocolMessageValidatorType<V, W> inValidator)
  {
    this.validator =
      Objects.requireNonNull(inValidator, "validator");
  }

  @Override
  public NPU1ComparisonFuzzy<W> convertToWire(
    final NPComparisonFuzzyType<V> message)
    throws NPProtocolException
  {
    if (message instanceof NPComparisonFuzzyType.Anything<V>) {
      return new NPU1ComparisonFuzzy.Anything<>();
    }

    if (message instanceof final NPComparisonFuzzyType.IsEqualTo<V> e) {
      return new NPU1ComparisonFuzzy.IsEqualTo<>(
        this.validator.convertToWire(e.value())
      );
    }

    if (message instanceof final NPComparisonFuzzyType.IsNotEqualTo<V> e) {
      return new NPU1ComparisonFuzzy.IsNotEqualTo<>(
        this.validator.convertToWire(e.value())
      );
    }

    if (message instanceof final NPComparisonFuzzyType.IsSimilarTo<V> e) {
      return new NPU1ComparisonFuzzy.IsSimilarTo<>(
        this.validator.convertToWire(e.value())
      );
    }

    if (message instanceof final NPComparisonFuzzyType.IsNotSimilarTo<V> e) {
      return new NPU1ComparisonFuzzy.IsNotSimilarTo<>(
        this.validator.convertToWire(e.value())
      );
    }

    throw new IllegalStateException(
      "Unrecognized message: %s".formatted(message)
    );
  }

  @Override
  public NPComparisonFuzzyType<V> convertFromWire(
    final NPU1ComparisonFuzzy<W> message)
    throws NPProtocolException
  {
    if (message instanceof NPU1ComparisonFuzzy.Anything<W>) {
      return new NPComparisonFuzzyType.Anything<>();
    }

    if (message instanceof final NPU1ComparisonFuzzy.IsEqualTo<W> e) {
      return new NPComparisonFuzzyType.IsEqualTo<>(
        this.validator.convertFromWire(e.fieldValue())
      );
    }

    if (message instanceof final NPU1ComparisonFuzzy.IsNotEqualTo<W> e) {
      return new NPComparisonFuzzyType.IsNotEqualTo<>(
        this.validator.convertFromWire(e.fieldValue())
      );
    }

    if (message instanceof final NPU1ComparisonFuzzy.IsSimilarTo<W> e) {
      return new NPComparisonFuzzyType.IsSimilarTo<>(
        this.validator.convertFromWire(e.fieldValue())
      );
    }

    if (message instanceof final NPU1ComparisonFuzzy.IsNotSimilarTo<W> e) {
      return new NPComparisonFuzzyType.IsNotSimilarTo<>(
        this.validator.convertFromWire(e.fieldValue())
      );
    }

    throw new IllegalStateException(
      "Unrecognized message: %s".formatted(message)
    );
  }
}
