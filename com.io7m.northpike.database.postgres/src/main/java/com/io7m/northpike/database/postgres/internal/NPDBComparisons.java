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


package com.io7m.northpike.database.postgres.internal;

import com.io7m.northpike.model.comparisons.NPComparisonExactType;
import com.io7m.northpike.model.comparisons.NPComparisonFuzzyType;
import com.io7m.northpike.model.comparisons.NPComparisonSetType;
import com.io7m.northpike.model.plans.NPPlanIdentifier;
import org.jooq.Condition;
import org.jooq.DSLContext;
import org.jooq.TableField;
import org.jooq.impl.DSL;

import static com.io7m.northpike.database.postgres.internal.Tables.ASSIGNMENTS;
import static com.io7m.northpike.database.postgres.internal.Tables.PLANS;

/**
 * Functions to perform comparisons over fields/columns.
 */

public final class NPDBComparisons
{
  private NPDBComparisons()
  {

  }

  /**
   * Create a fuzzy match expression.
   *
   * @param query       The query
   * @param fieldExact  The "exact" field
   * @param fieldSearch The search field
   * @param <T>         The type of compared values
   *
   * @return A fuzzy match condition
   */

  public static <T> Condition createFuzzyMatchQuery(
    final NPComparisonFuzzyType<T> query,
    final TableField<org.jooq.Record, T> fieldExact,
    final String fieldSearch)
  {
    if (query instanceof NPComparisonFuzzyType.Anything<T>) {
      return DSL.trueCondition();
    }

    if (query instanceof final NPComparisonFuzzyType.IsEqualTo<T> isEqualTo) {
      return fieldExact.equal(isEqualTo.value());
    }

    if (query instanceof final NPComparisonFuzzyType.IsNotEqualTo<T> isNotEqualTo) {
      return fieldExact.notEqual(isNotEqualTo.value());
    }

    if (query instanceof final NPComparisonFuzzyType.IsSimilarTo<T> isSimilarTo) {
      return DSL.condition(
        "%s @@ websearch_to_tsquery(?)".formatted(fieldSearch),
        isSimilarTo.value()
      );
    }

    if (query instanceof final NPComparisonFuzzyType.IsNotSimilarTo<T> isNotSimilarTo) {
      return DSL.condition(
        "NOT (%s @@ websearch_to_tsquery(?))".formatted(fieldSearch),
        isNotSimilarTo.value()
      );
    }

    throw new IllegalStateException(
      "Unrecognized name query: %s".formatted(query)
    );
  }

  /**
   * Create an exact match expression.
   *
   * @param query      The query
   * @param fieldExact The "exact" field
   * @param <T>        The type of compared values
   *
   * @return An exact match condition
   */

  public static <T> Condition createExactMatchQuery(
    final NPComparisonExactType<T> query,
    final TableField<org.jooq.Record, T> fieldExact)
  {
    if (query instanceof NPComparisonExactType.Anything<T>) {
      return DSL.trueCondition();
    }

    if (query instanceof final NPComparisonExactType.IsEqualTo<T> isEqualTo) {
      return fieldExact.equal(isEqualTo.value());
    }

    if (query instanceof final NPComparisonExactType.IsNotEqualTo<T> isNotEqualTo) {
      return fieldExact.notEqual(isNotEqualTo.value());
    }

    throw new IllegalStateException(
      "Unrecognized name query: %s".formatted(query)
    );
  }

  /**
   * Create a set match expression.
   *
   * @param query The query
   * @param field The array-typed field
   *
   * @return An exact match condition
   */

  public static Condition createSetMatchQueryString(
    final NPComparisonSetType<String> query,
    final TableField<org.jooq.Record, String[]> field)
  {
    if (query instanceof NPComparisonSetType.Anything<String>) {
      return DSL.trueCondition();
    }

    if (query instanceof final NPComparisonSetType.IsEqualTo<String> isEqualTo) {
      final var set = isEqualTo.value();
      final var values = new String[set.size()];
      set.toArray(values);

      return DSL.condition(
        "(? <@ cast (? as text[])) AND (? @> cast (? as text[]))",
        field,
        DSL.array(values),
        field,
        DSL.array(values)
      );
    }

    if (query instanceof final NPComparisonSetType.IsNotEqualTo<String> isNotEqualTo) {
      final var set = isNotEqualTo.value();
      final var values = new String[set.size()];
      set.toArray(values);

      return DSL.condition(
        "NOT ((? <@ cast (? as text[])) AND (? @> cast (? as text[])))",
        field,
        DSL.array(values),
        field,
        DSL.array(values)
      );
    }

    if (query instanceof final NPComparisonSetType.IsSubsetOf<String> isSubsetOf) {
      final var set = isSubsetOf.value();
      final var values = new String[set.size()];
      set.toArray(values);

      return DSL.condition(
        "? <@ cast (? as text[])",
        field,
        DSL.array(values)
      );
    }

    if (query instanceof final NPComparisonSetType.IsSupersetOf<String> isSupersetOf) {
      final var set = isSupersetOf.value();
      final var values = new String[set.size()];
      set.toArray(values);

      return DSL.condition(
        "? @> cast (? as text[])",
        field,
        DSL.array(values)
      );
    }

    if (query instanceof final NPComparisonSetType.IsOverlapping<String> isOverlapping) {
      final var set = isOverlapping.value();
      final var values = new String[set.size()];
      set.toArray(values);

      return DSL.condition(
        "? && cast (? as text[])",
        field,
        DSL.array(values)
      );
    }

    throw new IllegalStateException(
      "Unrecognized set query: %s".formatted(query)
    );
  }

  /**
   * Create a set match expression.
   *
   * @param query The query
   * @param field The array-typed field
   *
   * @return An exact match condition
   */

  public static Condition createSetMatchQueryLong(
    final NPComparisonSetType<Long> query,
    final TableField<org.jooq.Record, Long[]> field)
  {
    if (query instanceof NPComparisonSetType.Anything<Long>) {
      return DSL.trueCondition();
    }

    if (query instanceof final NPComparisonSetType.IsEqualTo<Long> isEqualTo) {
      final var set = isEqualTo.value();
      final var values = new Long[set.size()];
      set.toArray(values);

      return DSL.condition(
        "(? <@ cast (? as bigint[])) AND (? @> cast (? as bigint[]))",
        field,
        DSL.array(values),
        field,
        DSL.array(values)
      );
    }

    if (query instanceof final NPComparisonSetType.IsNotEqualTo<Long> isNotEqualTo) {
      final var set = isNotEqualTo.value();
      final var values = new Long[set.size()];
      set.toArray(values);

      return DSL.condition(
        "NOT ((? <@ cast (? as bigint[])) AND (? @> cast (? as bigint[])))",
        field,
        DSL.array(values),
        field,
        DSL.array(values)
      );
    }

    if (query instanceof final NPComparisonSetType.IsSubsetOf<Long> isSubsetOf) {
      final var set = isSubsetOf.value();
      final var values = new Long[set.size()];
      set.toArray(values);

      return DSL.condition(
        "? <@ cast (? as bigint[])",
        field,
        DSL.array(values)
      );
    }

    if (query instanceof final NPComparisonSetType.IsSupersetOf<Long> isSupersetOf) {
      final var set = isSupersetOf.value();
      final var values = new Long[set.size()];
      set.toArray(values);

      return DSL.condition(
        "? @> cast (? as bigint[])",
        field,
        DSL.array(values)
      );
    }

    if (query instanceof final NPComparisonSetType.IsOverlapping<Long> isOverlapping) {
      final var set = isOverlapping.value();
      final var values = new Long[set.size()];
      set.toArray(values);

      return DSL.condition(
        "? && cast (? as bigint[])",
        field,
        DSL.array(values)
      );
    }

    throw new IllegalStateException(
      "Unrecognized set query: %s".formatted(query)
    );
  }

  /**
   * Create a plan match expression.
   *
   * @param context The context
   * @param plan    The plan
   *
   * @return An exact match condition
   */

  public static Condition createAssignmentPlanCondition(
    final DSLContext context,
    final NPComparisonExactType<NPPlanIdentifier> plan)
  {
    if (plan instanceof NPComparisonExactType.Anything<NPPlanIdentifier>) {
      return DSL.trueCondition();
    }

    if (plan instanceof final NPComparisonExactType.IsEqualTo<NPPlanIdentifier> isEqualTo) {
      final var id = isEqualTo.value();
      return ASSIGNMENTS.A_PLAN.eq(
        context.select(PLANS.P_ID)
          .from(PLANS)
          .where(
            PLANS.P_NAME.eq(id.name().name().value())
              .and(PLANS.P_VERSION.eq(Long.valueOf(id.version())))
          )
      );
    }

    if (plan instanceof final NPComparisonExactType.IsNotEqualTo<NPPlanIdentifier> isNotEqualTo) {
      final var id = isNotEqualTo.value();
      return ASSIGNMENTS.A_PLAN.ne(
        context.select(PLANS.P_ID)
          .from(PLANS)
          .where(
            PLANS.P_NAME.eq(id.name().name().value())
              .and(PLANS.P_VERSION.eq(Long.valueOf(id.version())))
          )
      );
    }

    throw new IllegalStateException("Unrecognized match: %s".formatted(plan));
  }
}
