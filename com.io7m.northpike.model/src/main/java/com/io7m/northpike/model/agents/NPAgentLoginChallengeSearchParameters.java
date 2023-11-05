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


package com.io7m.northpike.model.agents;

import com.io7m.northpike.model.NPPageSizes;
import com.io7m.northpike.model.NPSearchParametersType;
import com.io7m.northpike.model.NPTimeRange;

import java.util.Objects;

/**
 * The search parameters for the agent login challenges.
 *
 * @param timeRange Limit events to the given time range
 * @param pageSize  The page size
 */

public record NPAgentLoginChallengeSearchParameters(
  NPTimeRange timeRange,
  long pageSize)
  implements NPSearchParametersType
{
  /**
   * The search parameters for the agent login challenges.
   *
   * @param timeRange Limit events to the given time range
   * @param pageSize  The page size
   */

  public NPAgentLoginChallengeSearchParameters
  {
    Objects.requireNonNull(timeRange, "timeRange");
    pageSize = NPPageSizes.clampPageSize(pageSize);
  }
}
