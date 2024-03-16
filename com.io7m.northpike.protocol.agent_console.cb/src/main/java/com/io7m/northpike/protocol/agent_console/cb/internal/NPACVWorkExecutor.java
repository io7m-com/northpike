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

import com.io7m.cedarbridge.runtime.api.CBOptionType;
import com.io7m.cedarbridge.runtime.api.CBString;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecName;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorConfiguration;
import com.io7m.northpike.protocol.agent_console.cb.NPAC1WorkExecutorConfiguration;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

import java.nio.file.Paths;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;
import static com.io7m.northpike.protocol.agent_console.cb.internal.NPACVWorkExecutorContainerImage.WORK_EXECUTOR_CONTAINER_IMAGE;

/**
 * A validator.
 */

public enum NPACVWorkExecutor
  implements NPProtocolMessageValidatorType<
  NPAWorkExecutorConfiguration, NPAC1WorkExecutorConfiguration>
{
  /**
   * A validator.
   */

  WORK_EXECUTOR;

  @Override
  public NPAC1WorkExecutorConfiguration convertToWire(
    final NPAWorkExecutorConfiguration message)
  {
    return new NPAC1WorkExecutorConfiguration(
      string(message.type().toString()),
      string(message.workDirectory().toString()),
      string(message.temporaryDirectory().toString()),
      CBOptionType.fromOptional(
        message.workExecDistributionDirectory()
          .map(x -> string(x.toString()))
      ),
      CBOptionType.fromOptional(
        message.containerImage()
          .map(WORK_EXECUTOR_CONTAINER_IMAGE::convertToWire)
      )
    );
  }

  @Override
  public NPAWorkExecutorConfiguration convertFromWire(
    final NPAC1WorkExecutorConfiguration message)
  {
    final var builder = NPAWorkExecutorConfiguration.builder();
    builder.setExecutorType(NPAWorkExecName.of(message.fieldType().value()));

    message.fieldContainerImage()
      .asOptional()
      .map(WORK_EXECUTOR_CONTAINER_IMAGE::convertFromWire)
      .ifPresent(builder::setContainerImage);

    builder.setWorkDirectory(
      Paths.get(message.fieldWorkDirectory().value())
    );

    builder.setTemporaryDirectory(
      Paths.get(message.fieldTemporaryDirectory().value())
    );

    message.fieldWorkExecDistributionDirectory()
      .asOptional()
      .map(CBString::value)
      .map(Paths::get)
      .ifPresent(builder::setWorkExecDistributionDirectory);

    return builder.build();
  }
}
