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

package com.io7m.northpike.strings;

import com.io7m.jxtrand.vanilla.JXTAbstractGenericStrings;
import com.io7m.repetoir.core.RPServiceType;

import java.util.Locale;

/**
 * The string resources.
 */

public final class NPStrings
  extends JXTAbstractGenericStrings<NPStringConstantType>
  implements RPServiceType
{
  /**
   * The string resources.
   *
   * @param locale The application locale
   */

  private NPStrings(
    final Locale locale)
  {
    super(
      locale,
      NPStrings.class,
      "/com/io7m/northpike/strings",
      "Messages"
    );
  }

  @Override
  public String format(
    final NPStringConstantType id,
    final Object... args)
  {
    if (id instanceof final NPStringConstantApplied app) {
      return this.format(app.constant(), app.args());
    }
    return super.format(id, args);
  }

  /**
   * Create string resources.
   *
   * @param locale The locale
   *
   * @return The string resources
   */

  public static NPStrings create(
    final Locale locale)
  {
    return new NPStrings(locale);
  }

  @Override
  public String toString()
  {
    return String.format(
      "[NPStrings 0x%08x]",
      Integer.valueOf(this.hashCode())
    );
  }

  @Override
  public String description()
  {
    return "String resource service.";
  }
}
