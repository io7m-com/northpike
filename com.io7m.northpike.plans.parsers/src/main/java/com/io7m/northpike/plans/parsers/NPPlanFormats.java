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


package com.io7m.northpike.plans.parsers;

import com.io7m.northpike.model.NPFormatName;
import com.io7m.northpike.model.plans.NPPlanFormatDescription;

import java.util.Set;

/**
 * The available plan formats.
 */

public final class NPPlanFormats
{
  private static final NPPlanFormatDescription XML_V1 =
    new NPPlanFormatDescription(
      NPFormatName.of("com.io7m.northpike.plans.parsers.v1"),
      "The v1 XML Plan format."
    );

  private NPPlanFormats()
  {

  }

  /**
   * @return The XML v1 format
   */

  public static NPPlanFormatDescription xml1()
  {
    return XML_V1;
  }

  /**
   * @return The supported formats
   */

  public static Set<NPPlanFormatDescription> formats()
  {
    return Set.of(xml1());
  }
}
