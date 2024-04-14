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


package com.io7m.northpike.protocol.user.cb.internal;

import com.io7m.northpike.model.NPWorkItemStatus;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1WorkItemStatus;

/**
 * A validator.
 */

public enum NPUVWorkItemStatus
  implements NPProtocolMessageValidatorType<NPWorkItemStatus, NPU1WorkItemStatus>
{
  /**
   * A validator.
   */

  WORK_ITEM_STATUS;

  @Override
  public NPU1WorkItemStatus convertToWire(
    final NPWorkItemStatus message)
  {
    return switch (message) {
      case WORK_ITEM_CREATED -> new NPU1WorkItemStatus.Created();
      case WORK_ITEM_ACCEPTED -> new NPU1WorkItemStatus.Accepted();
      case WORK_ITEM_RUNNING -> new NPU1WorkItemStatus.Running();
      case WORK_ITEM_SUCCEEDED -> new NPU1WorkItemStatus.Succeeded();
      case WORK_ITEM_FAILED -> new NPU1WorkItemStatus.Failed();
    };
  }

  @Override
  public NPWorkItemStatus convertFromWire(
    final NPU1WorkItemStatus message)
  {
    return switch (message) {
      case final NPU1WorkItemStatus.Accepted accepted ->
        NPWorkItemStatus.WORK_ITEM_ACCEPTED;
      case final NPU1WorkItemStatus.Created created ->
        NPWorkItemStatus.WORK_ITEM_CREATED;
      case final NPU1WorkItemStatus.Failed failed ->
        NPWorkItemStatus.WORK_ITEM_FAILED;
      case final NPU1WorkItemStatus.Running running ->
        NPWorkItemStatus.WORK_ITEM_RUNNING;
      case final NPU1WorkItemStatus.Succeeded succeeded ->
        NPWorkItemStatus.WORK_ITEM_SUCCEEDED;
    };
  }
}
