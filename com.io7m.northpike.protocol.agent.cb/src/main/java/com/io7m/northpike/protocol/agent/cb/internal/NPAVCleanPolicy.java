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

import com.io7m.northpike.model.NPCleanImmediately;
import com.io7m.northpike.model.NPCleanLater;
import com.io7m.northpike.model.NPCleanPolicyType;
import com.io7m.northpike.protocol.agent.cb.NPA1CleanPolicy;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

import static com.io7m.northpike.model.NPCleanImmediately.CLEAN_IMMEDIATELY;
import static com.io7m.northpike.model.NPCleanLater.CLEAN_LATER;

/**
 * A validator.
 */

public enum NPAVCleanPolicy
  implements NPProtocolMessageValidatorType<NPCleanPolicyType, NPA1CleanPolicy>
{
  /**
   * A validator.
   */

  CLEAN_POLICY;

  @Override
  public NPA1CleanPolicy convertToWire(
    final NPCleanPolicyType message)
  {
    return switch (message) {
      case final NPCleanImmediately c -> new NPA1CleanPolicy.CleanImmediately();
      case final NPCleanLater c -> new NPA1CleanPolicy.CleanLater();
    };
  }

  @Override
  public NPCleanPolicyType convertFromWire(
    final NPA1CleanPolicy message)
  {
    return switch (message) {
      case NPA1CleanPolicy.CleanImmediately c -> CLEAN_IMMEDIATELY;
      case NPA1CleanPolicy.CleanLater c -> CLEAN_LATER;
    };
  }
}
