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


package com.io7m.northpike.protocol.agent_console.cb.internal;

import com.io7m.cedarbridge.runtime.convenience.CBLists;
import com.io7m.cedarbridge.runtime.convenience.CBSets;
import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecName;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorPropertyCustom;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorPropertyStandard;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorPropertyType;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorSummary;
import com.io7m.northpike.protocol.agent_console.cb.NPAC1WorkExecutorSummary;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;

/**
 * A validator.
 */

public enum NPACVWorkExecSummary
  implements NPProtocolMessageValidatorType<
  NPAWorkExecutorSummary, NPAC1WorkExecutorSummary>
{
  /**
   * A validator.
   */

  WORK_EXECUTOR_SUMMARY;

  @Override
  public NPAC1WorkExecutorSummary convertToWire(
    final NPAWorkExecutorSummary message)
  {
    return new NPAC1WorkExecutorSummary(
      string(message.name().toString()),
      string(message.description()),
      CBLists.ofCollection(
        message.properties(),
        p -> string(p.toString())
      )
    );
  }

  @Override
  public NPAWorkExecutorSummary convertFromWire(
    final NPAC1WorkExecutorSummary message)
  {
    return new NPAWorkExecutorSummary(
      NPAWorkExecName.of(message.fieldName().value()),
      message.fieldDescription().value(),
      CBSets.toSet(
        message.fieldProperties(),
        x -> parseProperty(x.value())
      )
    );
  }

  private static NPAWorkExecutorPropertyType parseProperty(
    final String value)
  {
    try {
      return NPAWorkExecutorPropertyStandard.valueOf(value);
    } catch (final IllegalArgumentException e) {
      return new NPAWorkExecutorPropertyCustom(new RDottedName(value));
    }
  }
}
