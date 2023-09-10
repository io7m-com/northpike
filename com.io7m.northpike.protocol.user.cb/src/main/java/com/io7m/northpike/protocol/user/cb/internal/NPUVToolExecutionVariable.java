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

import com.io7m.cedarbridge.runtime.api.CBBooleanType;
import com.io7m.cedarbridge.runtime.api.CBCore;
import com.io7m.cedarbridge.runtime.api.CBString;
import com.io7m.cedarbridge.runtime.convenience.CBLists;
import com.io7m.cedarbridge.runtime.convenience.CBSets;
import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1ToolExecutionVariable;
import com.io7m.northpike.toolexec.model.NPTXPlanVariableBoolean;
import com.io7m.northpike.toolexec.model.NPTXPlanVariableInteger;
import com.io7m.northpike.toolexec.model.NPTXPlanVariableString;
import com.io7m.northpike.toolexec.model.NPTXPlanVariableStringSet;
import com.io7m.northpike.toolexec.model.NPTXPlanVariableType;

import static com.io7m.cedarbridge.runtime.api.CBCore.signed64;
import static com.io7m.cedarbridge.runtime.api.CBCore.string;

/**
 * A validator.
 */

public enum NPUVToolExecutionVariable
  implements NPProtocolMessageValidatorType<NPTXPlanVariableType, NPU1ToolExecutionVariable>
{
  /**
   * A validator.
   */

  TOOL_EXECUTION_VARIABLE;

  @Override
  public NPU1ToolExecutionVariable convertToWire(
    final NPTXPlanVariableType message)
  {
    if (message instanceof final NPTXPlanVariableString s) {
      return new NPU1ToolExecutionVariable.String(
        string(s.name().value()),
        string(s.value())
      );
    }

    if (message instanceof final NPTXPlanVariableStringSet s) {
      return new NPU1ToolExecutionVariable.StringSet(
        string(s.name().value()),
        CBLists.ofCollection(s.value(), CBCore::string)
      );
    }

    if (message instanceof final NPTXPlanVariableBoolean s) {
      return new NPU1ToolExecutionVariable.Boolean(
        string(s.name().value()),
        CBBooleanType.fromBoolean(s.value())
      );
    }

    if (message instanceof final NPTXPlanVariableInteger s) {
      return new NPU1ToolExecutionVariable.Integer(
        string(s.name().value()),
        signed64(s.value())
      );
    }

    throw new IllegalStateException(
      "Unrecognized message: %s".formatted(message)
    );
  }

  @Override
  public NPTXPlanVariableType convertFromWire(
    final NPU1ToolExecutionVariable message)
  {
    if (message instanceof final NPU1ToolExecutionVariable.String s) {
      return new NPTXPlanVariableString(
        new RDottedName(s.fieldName().value()),
        s.fieldValue().value()
      );
    }

    if (message instanceof final NPU1ToolExecutionVariable.StringSet s) {
      return new NPTXPlanVariableStringSet(
        new RDottedName(s.fieldName().value()),
        CBSets.toSet(s.fieldValue(), CBString::value)
      );
    }

    if (message instanceof final NPU1ToolExecutionVariable.Boolean s) {
      return new NPTXPlanVariableBoolean(
        new RDottedName(s.fieldName().value()),
        s.fieldValue().asBoolean()
      );
    }

    if (message instanceof final NPU1ToolExecutionVariable.Integer s) {
      return new NPTXPlanVariableInteger(
        new RDottedName(s.fieldName().value()),
        s.fieldValue().value()
      );
    }

    throw new IllegalStateException(
      "Unrecognized message: %s".formatted(message)
    );
  }
}
