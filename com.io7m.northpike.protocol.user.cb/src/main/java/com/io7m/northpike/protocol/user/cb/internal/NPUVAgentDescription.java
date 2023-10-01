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
import com.io7m.cedarbridge.runtime.convenience.CBMaps;
import com.io7m.northpike.model.NPAgentDescription;
import com.io7m.northpike.model.NPAgentID;
import com.io7m.northpike.model.NPAgentLabelName;
import com.io7m.northpike.model.NPKey;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1AgentDescription;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVAgentLabel.AGENT_LABEL;

/**
 * A validator.
 */

public enum NPUVAgentDescription
  implements NPProtocolMessageValidatorType<
  NPAgentDescription, NPU1AgentDescription>
{
  /**
   * A validator.
   */

  AGENT_DESCRIPTION;

  @Override
  public NPU1AgentDescription convertToWire(
    final NPAgentDescription message)
  {
    return new NPU1AgentDescription(
      new CBUUID(message.id().value()),
      string(message.name()),
      string(message.accessKey().format()),
      CBMaps.ofMapString(message.environmentVariables()),
      CBMaps.ofMapString(message.systemProperties()),
      CBMaps.ofMap(
        message.labels(),
        name -> string(name.value().value()),
        AGENT_LABEL::convertToWire
      )
    );
  }

  @Override
  public NPAgentDescription convertFromWire(
    final NPU1AgentDescription message)
  {
    return new NPAgentDescription(
      new NPAgentID(message.fieldId().value()),
      message.fieldName().value(),
      NPKey.parse(message.fieldAccessKey().value()),
      CBMaps.toMapString(message.fieldEnvironmentVariables()),
      CBMaps.toMapString(message.fieldSystemProperties()),
      CBMaps.toMap(
        message.fieldLabels(),
        name -> NPAgentLabelName.of(name.value()),
        AGENT_LABEL::convertFromWire
      )
    );
  }
}
