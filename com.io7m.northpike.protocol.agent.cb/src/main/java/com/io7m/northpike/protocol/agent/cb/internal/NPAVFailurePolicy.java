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

import com.io7m.northpike.model.NPFailureFail;
import com.io7m.northpike.model.NPFailureIgnore;
import com.io7m.northpike.model.NPFailurePolicyType;
import com.io7m.northpike.model.NPFailureRetry;
import com.io7m.northpike.protocol.agent.cb.NPA1FailurePolicy;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

import static com.io7m.cedarbridge.runtime.api.CBCore.unsigned32;
import static com.io7m.northpike.model.NPFailureFail.FAIL;
import static com.io7m.northpike.model.NPFailureIgnore.IGNORE_FAILURE;

/**
 * A validator.
 */

public enum NPAVFailurePolicy
  implements NPProtocolMessageValidatorType<NPFailurePolicyType, NPA1FailurePolicy>
{
  /**
   * A validator.
   */

  FAILURE_POLICY;

  @Override
  public NPA1FailurePolicy convertToWire(
    final NPFailurePolicyType message)
  {
    return switch (message) {
      case final NPFailureFail f -> new NPA1FailurePolicy.Fail();
      case final NPFailureIgnore i -> new NPA1FailurePolicy.Ignore();
      case final NPFailureRetry retry ->
        new NPA1FailurePolicy.Retry(unsigned32(retry.retryCount()));
    };
  }

  @Override
  public NPFailurePolicyType convertFromWire(
    final NPA1FailurePolicy message)
  {
    return switch (message) {
      case final NPA1FailurePolicy.Fail fail -> FAIL;
      case final NPA1FailurePolicy.Ignore ignore -> IGNORE_FAILURE;
      case final NPA1FailurePolicy.Retry retry ->
        new NPFailureRetry((int) retry.fieldRetryCount().value());
    };
  }
}
