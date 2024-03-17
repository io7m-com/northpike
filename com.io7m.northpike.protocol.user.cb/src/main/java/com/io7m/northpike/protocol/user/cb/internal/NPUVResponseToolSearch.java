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

import com.io7m.cedarbridge.runtime.api.CBUUID;
import com.io7m.cedarbridge.runtime.convenience.CBLists;
import com.io7m.northpike.model.NPPage;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.NPUResponseToolSearch;
import com.io7m.northpike.protocol.user.cb.NPU1Page;
import com.io7m.northpike.protocol.user.cb.NPU1ResponseToolSearch;

import static com.io7m.cedarbridge.runtime.api.CBCore.unsigned32;
import static com.io7m.cedarbridge.runtime.api.CBCore.unsigned64;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVToolSummary.TOOL_SUMMARY;

/**
 * A validator.
 */

public enum NPUVResponseToolSearch
  implements NPProtocolMessageValidatorType<
  NPUResponseToolSearch,
  NPU1ResponseToolSearch>
{
  /**
   * A validator.
   */

  RESPONSE_TOOL_SEARCH;

  @Override
  public NPU1ResponseToolSearch convertToWire(
    final NPUResponseToolSearch message)
  {
    return new NPU1ResponseToolSearch(
      new CBUUID(message.messageID()),
      new CBUUID(message.correlationID()),
      new NPU1Page<>(
        CBLists.ofCollection(
          message.results().items(),
          TOOL_SUMMARY::convertToWire
        ),
        unsigned32(message.results().pageIndex()),
        unsigned32(message.results().pageCount()),
        unsigned64(message.results().pageFirstOffset())
      )
    );
  }

  @Override
  public NPUResponseToolSearch convertFromWire(
    final NPU1ResponseToolSearch message)
  {
    return new NPUResponseToolSearch(
      message.fieldMessageId().value(),
      message.fieldCorrelationId().value(),
      new NPPage<>(
        CBLists.toList(
          message.fieldResults().fieldItems(),
          TOOL_SUMMARY::convertFromWire
        ),
        (int) message.fieldResults().fieldPageIndex().value(),
        (int) message.fieldResults().fieldPageCount().value(),
        message.fieldResults().fieldPageFirstOffset().value()
      )
    );
  }
}
