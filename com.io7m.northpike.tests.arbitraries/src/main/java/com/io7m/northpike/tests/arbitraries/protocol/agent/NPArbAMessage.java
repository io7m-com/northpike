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


package com.io7m.northpike.tests.arbitraries.protocol.agent;

import com.io7m.northpike.protocol.agent.NPACommandCDisconnect;
import com.io7m.northpike.protocol.agent.NPACommandCEnvironmentInfo;
import com.io7m.northpike.protocol.agent.NPACommandCLogin;
import com.io7m.northpike.protocol.agent.NPACommandCWorkItemFailed;
import com.io7m.northpike.protocol.agent.NPACommandCWorkItemOutput;
import com.io7m.northpike.protocol.agent.NPACommandCWorkItemStarted;
import com.io7m.northpike.protocol.agent.NPACommandCWorkItemSucceeded;
import com.io7m.northpike.protocol.agent.NPACommandSLatencyCheck;
import com.io7m.northpike.protocol.agent.NPACommandSWorkOffered;
import com.io7m.northpike.protocol.agent.NPACommandSWorkSent;
import com.io7m.northpike.protocol.agent.NPAMessageType;
import com.io7m.northpike.protocol.agent.NPAResponseError;
import com.io7m.northpike.protocol.agent.NPAResponseLatencyCheck;
import com.io7m.northpike.protocol.agent.NPAResponseOK;
import com.io7m.northpike.tests.arbitraries.NPArbAbstract;
import net.jqwik.api.Arbitraries;

import java.util.stream.Collectors;
import java.util.stream.Stream;

public final class NPArbAMessage extends NPArbAbstract<NPAMessageType>
{
  public NPArbAMessage()
  {
    super(
      NPAMessageType.class,
      () -> {
        return Arbitraries.oneOf(
          Stream.of(
              NPACommandCDisconnect.class,
              NPACommandCEnvironmentInfo.class,
              NPACommandCLogin.class,
              NPACommandCWorkItemFailed.class,
              NPACommandCWorkItemOutput.class,
              NPACommandCWorkItemStarted.class,
              NPACommandCWorkItemSucceeded.class,
              NPACommandSLatencyCheck.class,
              NPAResponseError.class,
              NPAResponseLatencyCheck.class,
              NPAResponseOK.class,
              NPACommandSWorkOffered.class,
              NPACommandSWorkSent.class
            ).map(Arbitraries::defaultFor)
            .collect(Collectors.toUnmodifiableList())
        );
      }
    );
  }
}
