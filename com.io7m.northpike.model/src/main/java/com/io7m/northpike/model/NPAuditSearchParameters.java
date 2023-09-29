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

import com.io7m.northpike.model.comparisons.NPComparisonExactType;

import java.util.Objects;
import java.util.Optional;

/**
 * The search parameters for the audit log.
 *
 * @param owner     Limit events to the given owner
 * @param type      Limit events to the given type
 * @param timeRange Limit events to the given time range
 * @param pageSize  The page size
 */

public record NPAuditSearchParameters(
  Optional<NPAuditUserOrAgentType> owner,
  NPComparisonExactType<String> type,
  NPTimeRange timeRange,
  long pageSize)
  implements NPSearchParametersType
{
  /**
   * The search parameters for the audit log.
   *
   * @param owner     Limit events to the given owner
   * @param type      Limit events to the given type
   * @param timeRange Limit events to the given time range
   * @param pageSize  The page size
   */

  public NPAuditSearchParameters
  {
    Objects.requireNonNull(owner, "owner");
    Objects.requireNonNull(type, "type");
    Objects.requireNonNull(timeRange, "timeRange");
    pageSize = NPPageSizes.clampPageSize(pageSize);
  }
}
