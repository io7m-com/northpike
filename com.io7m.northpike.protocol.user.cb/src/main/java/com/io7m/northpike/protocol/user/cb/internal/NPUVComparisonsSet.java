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
import com.io7m.cedarbridge.runtime.convenience.CBLists;
import com.io7m.cedarbridge.runtime.convenience.CBSets;
import com.io7m.northpike.model.NPValidityException;
import com.io7m.northpike.model.comparisons.NPComparisonSetType;
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1ComparisonSet;

import java.util.Objects;

/**
 * Set comparisons.
 *
 * @param <V> The type of model values
 * @param <W> The type of serialized values
 */

public final class NPUVComparisonsSet<V, W extends CBSerializableType>
  implements NPProtocolMessageValidatorType<
  NPComparisonSetType<V>,
  NPU1ComparisonSet<W>>
{
  private final NPProtocolMessageValidatorType<V, W> validator;

  /**
   * Set comparisons.
   *
   * @param inValidator A validator for values
   */

  public NPUVComparisonsSet(
    final NPProtocolMessageValidatorType<V, W> inValidator)
  {
    this.validator =
      Objects.requireNonNull(inValidator, "validator");
  }

  @Override
  public NPU1ComparisonSet<W> convertToWire(
    final NPComparisonSetType<V> message)
    throws NPProtocolException
  {
    if (message instanceof NPComparisonSetType.Anything<V>) {
      return new NPU1ComparisonSet.Anything<>();
    }

    if (message instanceof final NPComparisonSetType.IsEqualTo<V> e) {
      return new NPU1ComparisonSet.IsEqualTo<>(
        CBLists.ofCollection(e.value(), this::convertToWireQuiet)
      );
    }

    if (message instanceof final NPComparisonSetType.IsNotEqualTo<V> e) {
      return new NPU1ComparisonSet.IsNotEqualTo<>(
        CBLists.ofCollection(e.value(), this::convertToWireQuiet)
      );
    }

    if (message instanceof final NPComparisonSetType.IsSubsetOf<V> e) {
      return new NPU1ComparisonSet.IsSubsetOf<>(
        CBLists.ofCollection(e.value(), this::convertToWireQuiet)
      );
    }

    if (message instanceof final NPComparisonSetType.IsSupersetOf<V> e) {
      return new NPU1ComparisonSet.IsSupersetOf<>(
        CBLists.ofCollection(e.value(), this::convertToWireQuiet)
      );
    }

    if (message instanceof final NPComparisonSetType.IsOverlapping<V> e) {
      return new NPU1ComparisonSet.IsOverlapping<>(
        CBLists.ofCollection(e.value(), this::convertToWireQuiet)
      );
    }

    throw new IllegalStateException(
      "Unrecognized message: %s".formatted(message)
    );
  }

  private W convertToWireQuiet(
    final V m)
  {
    try {
      return this.validator.convertToWire(m);
    } catch (final NPProtocolException e) {
      throw new NPValidityException(e.getMessage(), e);
    }
  }

  private V convertFromWireQuiet(
    final W m)
  {
    try {
      return this.validator.convertFromWire(m);
    } catch (final NPProtocolException e) {
      throw new NPValidityException(e.getMessage(), e);
    }
  }

  @Override
  public NPComparisonSetType<V> convertFromWire(
    final NPU1ComparisonSet<W> message)
    throws NPProtocolException
  {
    if (message instanceof NPU1ComparisonSet.Anything<W>) {
      return new NPComparisonSetType.Anything<>();
    }

    if (message instanceof final NPU1ComparisonSet.IsEqualTo<W> e) {
      return new NPComparisonSetType.IsEqualTo<>(
        CBSets.toSet(e.fieldValue(), this::convertFromWireQuiet)
      );
    }

    if (message instanceof final NPU1ComparisonSet.IsNotEqualTo<W> e) {
      return new NPComparisonSetType.IsNotEqualTo<>(
        CBSets.toSet(e.fieldValue(), this::convertFromWireQuiet)
      );
    }

    if (message instanceof final NPU1ComparisonSet.IsSubsetOf<W> e) {
      return new NPComparisonSetType.IsSubsetOf<>(
        CBSets.toSet(e.fieldValue(), this::convertFromWireQuiet)
      );
    }

    if (message instanceof final NPU1ComparisonSet.IsSupersetOf<W> e) {
      return new NPComparisonSetType.IsSupersetOf<>(
        CBSets.toSet(e.fieldValue(), this::convertFromWireQuiet)
      );
    }

    if (message instanceof final NPU1ComparisonSet.IsOverlapping<W> e) {
      return new NPComparisonSetType.IsOverlapping<>(
        CBSets.toSet(e.fieldValue(), this::convertFromWireQuiet)
      );
    }

    throw new IllegalStateException(
      "Unrecognized message: %s".formatted(message)
    );
  }
}
