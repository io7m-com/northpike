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


package com.io7m.northpike.model;

import com.io7m.medrina.api.MRoleName;
import com.io7m.northpike.model.comparisons.NPComparisonFuzzyType;
import com.io7m.northpike.model.comparisons.NPComparisonSetType;

import java.util.Objects;

/**
 * The parameters required to search users.
 *
 * @param name     The name match expression
 * @param roles    The role match expression
 * @param pageSize The page size
 */

public record NPUserSearchParameters(
  NPComparisonFuzzyType<String> name,
  NPComparisonSetType<MRoleName> roles,
  long pageSize)
  implements NPSearchParametersType
{
  /**
   * The parameters required to search users.
   *
   * @param name     The name match expression
   * @param roles    The role match expression
   * @param pageSize The page size
   */

  public NPUserSearchParameters
  {
    Objects.requireNonNull(name, "name");
    Objects.requireNonNull(roles, "roles");

    pageSize = NPPageSizes.clampPageSize(pageSize);
  }
}
