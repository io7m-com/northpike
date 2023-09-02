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

/**
 * The status of a work item.
 */

public enum NPWorkItemStatus
{
  /**
   * The work item has been created.
   */

  WORK_ITEM_CREATED,

  /**
   * The work item has been accepted by an agent.
   */

  WORK_ITEM_ACCEPTED,

  /**
   * The work item is running.
   */

  WORK_ITEM_RUNNING,

  /**
   * The work item succeeded.
   */

  WORK_ITEM_SUCCEEDED,

  /**
   * The work item failed.
   */

  WORK_ITEM_FAILED
}
