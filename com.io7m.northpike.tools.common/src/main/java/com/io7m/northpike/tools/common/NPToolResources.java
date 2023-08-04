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


package com.io7m.northpike.tools.common;

import com.io7m.jmulticlose.core.CloseableCollection;
import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.tools.api.NPToolException;

import java.util.Map;
import java.util.Optional;

import static com.io7m.northpike.strings.NPStringConstants.ERROR_RESOURCE_CLOSING;

/**
 * Convenience functions to create resource collections for tools.
 */

public final class NPToolResources
{
  private NPToolResources()
  {

  }

  /**
   * Create a resource collection.
   *
   * @param strings The string resources
   *
   * @return A new resource collection
   */

  public static CloseableCollectionType<NPToolException> createResourceCollection(
    final NPStrings strings)
  {
    return CloseableCollection.create(() -> new NPToolException(
      strings.format(ERROR_RESOURCE_CLOSING),
      new NPErrorCode("resources"),
      Map.of(),
      Optional.empty()
    ));
  }
}
