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

import com.io7m.cedarbridge.runtime.convenience.CBLists;
import com.io7m.cedarbridge.runtime.convenience.CBMaps;
import com.io7m.cedarbridge.runtime.convenience.CBSets;
import com.io7m.northpike.model.agents.NPAgentResourceName;
import com.io7m.northpike.model.agents.NPAgentWorkItem;
import com.io7m.northpike.protocol.agent.cb.NPA1AgentWorkItem;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

import static com.io7m.northpike.protocol.agent.cb.internal.NPAVArchiveLinks.ARCHIVE_LINKS;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVCleanPolicy.CLEAN_POLICY;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVFailurePolicy.FAILURE_POLICY;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVToolExecutionEvaluated.TOOL_EXECUTION_EVALUATED;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVToolReference.TOOL_REFERENCE;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVWorkItemIdentifier.WORK_ITEM_IDENTIFIER;

/**
 * A validator.
 */

public enum NPAVAgentWorkItem
  implements NPProtocolMessageValidatorType<NPAgentWorkItem, NPA1AgentWorkItem>
{
  /**
   * A validator.
   */

  AGENT_WORK_ITEM;

  @Override
  public NPA1AgentWorkItem convertToWire(
    final NPAgentWorkItem message)
  {
    return new NPA1AgentWorkItem(
      WORK_ITEM_IDENTIFIER.convertToWire(message.identifier()),
      CBMaps.ofMapString(message.metadata()),
      CBLists.ofCollection(
        message.toolsRequired(),
        TOOL_REFERENCE::convertToWire
      ),
      TOOL_EXECUTION_EVALUATED.convertToWire(message.toolExecution()),
      ARCHIVE_LINKS.convertToWire(message.archiveLinks()),
      CBLists.ofCollectionString(
        message.lockResources()
          .stream()
          .map(NPAgentResourceName::toString)
          .toList()),
      FAILURE_POLICY.convertToWire(message.failurePolicy()),
      CLEAN_POLICY.convertToWire(message.cleanPolicy())
    );
  }

  @Override
  public NPAgentWorkItem convertFromWire(
    final NPA1AgentWorkItem message)
  {
    return new NPAgentWorkItem(
      WORK_ITEM_IDENTIFIER.convertFromWire(message.fieldIdentifier()),
      CBMaps.toMapString(message.fieldMetadata()),
      CBSets.toSet(
        message.fieldToolsRequired(),
        TOOL_REFERENCE::convertFromWire
      ),
      TOOL_EXECUTION_EVALUATED.convertFromWire(message.fieldToolExecution()),
      ARCHIVE_LINKS.convertFromWire(message.fieldArchiveLinks()),
      CBSets.toSet(
        message.fieldLockResources(),
        s -> NPAgentResourceName.of(s.value())
      ),
      FAILURE_POLICY.convertFromWire(message.fieldFailurePolicy()),
      CLEAN_POLICY.convertFromWire(message.fieldCleanPolicy())
    );
  }
}
