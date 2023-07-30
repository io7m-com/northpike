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


package com.io7m.northpike.scm_repository.spi;

import java.util.Objects;
import java.util.UUID;

/**
 * A task is in progress.
 *
 * @param taskId   The task ID
 * @param progress The approximate progress in the range {@code [0, 1]}
 */

public record NPSCMTaskInProgress(
  UUID taskId,
  double progress)
  implements NPSCMEventTaskType
{
  /**
   * A task is in progress.
   *
   * @param taskId   The task ID
   * @param progress The approximate progress in the range {@code [0, 1]}
   */

  public NPSCMTaskInProgress
  {
    Objects.requireNonNull(taskId, "taskId");
  }
}
