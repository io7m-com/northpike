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


package com.io7m.northpike.server.internal;

import com.io7m.jmulticlose.core.CloseableCollection;
import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.jmulticlose.core.CloseableTracker;
import com.io7m.jmulticlose.core.CloseableTrackerType;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.server.api.NPServerException;

import java.util.Map;
import java.util.Optional;

/**
 * Functions to create closeable collections.
 */

public final class NPServerResources
{
  private NPServerResources()
  {

  }

  /**
   * @return A new closeable collection.
   */

  public static CloseableCollectionType<NPServerException> createResources()
  {
    return CloseableCollection.create(() -> {
      return new NPServerException(
        "One or more resources could not be closed.",
        new NPErrorCode("resources"),
        Map.of(),
        Optional.empty()
      );
    });
  }

  /**
   * @return A new closeable tracker.
   */

  public static CloseableTrackerType<NPServerException> createTracker()
  {
    return CloseableTracker.create(() -> {
      return new NPServerException(
        "One or more resources could not be closed.",
        new NPErrorCode("resources"),
        Map.of(),
        Optional.empty()
      );
    });
  }
}
