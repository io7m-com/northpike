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

package com.io7m.northpike.model.plans;

/**
 * A mutable builder for barriers.
 */

public interface NPPlanBarrierBuilderType
  extends NPPlanElementBuilderType
{
  @Override
  NPPlanBarrierBuilderType setDescription(
    String description)
    throws NPPlanException;

  @Override
  NPPlanBarrierBuilderType addDependsOn(
    NPPlanElementName target)
    throws NPPlanException;

  /**
   * Add a dependency on another element.
   *
   * @param target The target element
   *
   * @return this
   *
   * @throws NPPlanException On errors
   */

  default NPPlanBarrierBuilderType addDependsOn(
    final String target)
    throws NPPlanException
  {
    return this.addDependsOn(NPPlanElementName.of(target));
  }
}
