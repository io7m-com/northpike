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

package com.io7m.northpike.protocol.agent.cb.internal;

import com.io7m.cedarbridge.runtime.api.CBURI;
import com.io7m.northpike.model.NPArchiveLinks;
import com.io7m.northpike.protocol.agent.cb.NPA1ArchiveLinks;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

/**
 * A validator.
 */

public enum NPAVArchiveLinks
  implements NPProtocolMessageValidatorType<NPArchiveLinks, NPA1ArchiveLinks>
{
  /**
   * A validator.
   */

  ARCHIVE_LINKS;

  @Override
  public NPA1ArchiveLinks convertToWire(
    final NPArchiveLinks message)
  {
    return new NPA1ArchiveLinks(
      new CBURI(message.sources()),
      new CBURI(message.checksum())
    );
  }

  @Override
  public NPArchiveLinks convertFromWire(
    final NPA1ArchiveLinks message)
  {
    return new NPArchiveLinks(
      message.fieldFileURI().value(),
      message.fieldChecksumURI().value()
    );
  }
}
