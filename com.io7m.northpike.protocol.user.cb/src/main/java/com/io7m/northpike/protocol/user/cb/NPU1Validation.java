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

package com.io7m.northpike.protocol.user.cb;


import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.NPUCommandAgentGet;
import com.io7m.northpike.protocol.user.NPUCommandAgentLabelDelete;
import com.io7m.northpike.protocol.user.NPUCommandAgentLabelGet;
import com.io7m.northpike.protocol.user.NPUCommandAgentLabelPut;
import com.io7m.northpike.protocol.user.NPUCommandAgentLabelSearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandAgentLabelSearchNext;
import com.io7m.northpike.protocol.user.NPUCommandAgentLabelSearchPrevious;
import com.io7m.northpike.protocol.user.NPUCommandAgentPut;
import com.io7m.northpike.protocol.user.NPUCommandAgentSearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandAgentSearchNext;
import com.io7m.northpike.protocol.user.NPUCommandAgentSearchPrevious;
import com.io7m.northpike.protocol.user.NPUCommandAgentsConnected;
import com.io7m.northpike.protocol.user.NPUCommandAssignmentExecute;
import com.io7m.northpike.protocol.user.NPUCommandAssignmentExecutionDelete;
import com.io7m.northpike.protocol.user.NPUCommandAssignmentExecutionSearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandAssignmentExecutionSearchNext;
import com.io7m.northpike.protocol.user.NPUCommandAssignmentExecutionSearchPrevious;
import com.io7m.northpike.protocol.user.NPUCommandAssignmentExecutionWorkItems;
import com.io7m.northpike.protocol.user.NPUCommandAssignmentGet;
import com.io7m.northpike.protocol.user.NPUCommandAssignmentPut;
import com.io7m.northpike.protocol.user.NPUCommandAssignmentSearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandAssignmentSearchNext;
import com.io7m.northpike.protocol.user.NPUCommandAssignmentSearchPrevious;
import com.io7m.northpike.protocol.user.NPUCommandAuditSearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandAuditSearchNext;
import com.io7m.northpike.protocol.user.NPUCommandAuditSearchPrevious;
import com.io7m.northpike.protocol.user.NPUCommandDisconnect;
import com.io7m.northpike.protocol.user.NPUCommandLogin;
import com.io7m.northpike.protocol.user.NPUCommandPlanDelete;
import com.io7m.northpike.protocol.user.NPUCommandPlanGet;
import com.io7m.northpike.protocol.user.NPUCommandPlanPut;
import com.io7m.northpike.protocol.user.NPUCommandPlanSearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandPlanSearchNext;
import com.io7m.northpike.protocol.user.NPUCommandPlanSearchPrevious;
import com.io7m.northpike.protocol.user.NPUCommandPlanValidate;
import com.io7m.northpike.protocol.user.NPUCommandPublicKeyDelete;
import com.io7m.northpike.protocol.user.NPUCommandPublicKeyGet;
import com.io7m.northpike.protocol.user.NPUCommandPublicKeyPut;
import com.io7m.northpike.protocol.user.NPUCommandPublicKeySearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandPublicKeySearchNext;
import com.io7m.northpike.protocol.user.NPUCommandPublicKeySearchPrevious;
import com.io7m.northpike.protocol.user.NPUCommandRepositoryGet;
import com.io7m.northpike.protocol.user.NPUCommandRepositoryPublicKeyAssign;
import com.io7m.northpike.protocol.user.NPUCommandRepositoryPublicKeyUnassign;
import com.io7m.northpike.protocol.user.NPUCommandRepositoryPublicKeysAssigned;
import com.io7m.northpike.protocol.user.NPUCommandRepositoryPut;
import com.io7m.northpike.protocol.user.NPUCommandRepositorySearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandRepositorySearchNext;
import com.io7m.northpike.protocol.user.NPUCommandRepositorySearchPrevious;
import com.io7m.northpike.protocol.user.NPUCommandSCMProvidersSupported;
import com.io7m.northpike.protocol.user.NPUCommandSelf;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionGet;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionPut;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionSearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionSearchNext;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionSearchPrevious;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionValidate;
import com.io7m.northpike.protocol.user.NPUCommandType;
import com.io7m.northpike.protocol.user.NPUCommandUserRolesAssign;
import com.io7m.northpike.protocol.user.NPUCommandUserRolesGet;
import com.io7m.northpike.protocol.user.NPUCommandUserRolesRevoke;
import com.io7m.northpike.protocol.user.NPUCommandUserSearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandUserSearchNext;
import com.io7m.northpike.protocol.user.NPUCommandUserSearchPrevious;
import com.io7m.northpike.protocol.user.NPUCommandUsersConnected;
import com.io7m.northpike.protocol.user.NPUEventType;
import com.io7m.northpike.protocol.user.NPUMessageType;
import com.io7m.northpike.protocol.user.NPUResponseAgentGet;
import com.io7m.northpike.protocol.user.NPUResponseAgentLabelGet;
import com.io7m.northpike.protocol.user.NPUResponseAgentLabelSearch;
import com.io7m.northpike.protocol.user.NPUResponseAgentSearch;
import com.io7m.northpike.protocol.user.NPUResponseAgentsConnected;
import com.io7m.northpike.protocol.user.NPUResponseAssignmentExecutionSearch;
import com.io7m.northpike.protocol.user.NPUResponseAssignmentExecutionWorkItems;
import com.io7m.northpike.protocol.user.NPUResponseAssignmentGet;
import com.io7m.northpike.protocol.user.NPUResponseAssignmentSearch;
import com.io7m.northpike.protocol.user.NPUResponseAuditSearch;
import com.io7m.northpike.protocol.user.NPUResponseError;
import com.io7m.northpike.protocol.user.NPUResponseOK;
import com.io7m.northpike.protocol.user.NPUResponsePlanGet;
import com.io7m.northpike.protocol.user.NPUResponsePlanSearch;
import com.io7m.northpike.protocol.user.NPUResponsePlanValidate;
import com.io7m.northpike.protocol.user.NPUResponsePublicKeyGet;
import com.io7m.northpike.protocol.user.NPUResponsePublicKeySearch;
import com.io7m.northpike.protocol.user.NPUResponseRepositoryGet;
import com.io7m.northpike.protocol.user.NPUResponseRepositoryPublicKeysAssigned;
import com.io7m.northpike.protocol.user.NPUResponseRepositorySearch;
import com.io7m.northpike.protocol.user.NPUResponseSCMProvidersSupported;
import com.io7m.northpike.protocol.user.NPUResponseSelf;
import com.io7m.northpike.protocol.user.NPUResponseToolExecutionDescriptionGet;
import com.io7m.northpike.protocol.user.NPUResponseToolExecutionDescriptionSearch;
import com.io7m.northpike.protocol.user.NPUResponseToolExecutionDescriptionValidate;
import com.io7m.northpike.protocol.user.NPUResponseType;
import com.io7m.northpike.protocol.user.NPUResponseUserRolesGet;
import com.io7m.northpike.protocol.user.NPUResponseUserSearch;
import com.io7m.northpike.protocol.user.NPUResponseUsersConnected;

import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentGet.COMMAND_AGENT_GET;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentLabelDelete.COMMAND_AGENT_LABEL_DELETE;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentLabelGet.COMMAND_AGENT_LABEL_GET;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentLabelPut.COMMAND_AGENT_LABEL_PUT;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentLabelSearchBegin.COMMAND_AGENT_LABEL_SEARCH_BEGIN;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentLabelSearchNext.COMMAND_AGENT_LABEL_SEARCH_NEXT;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentLabelSearchPrevious.COMMAND_AGENT_LABEL_SEARCH_PREVIOUS;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentPut.COMMAND_AGENT_PUT;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentSearchBegin.COMMAND_AGENT_SEARCH_BEGIN;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentSearchNext.COMMAND_AGENT_SEARCH_NEXT;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentSearchPrevious.COMMAND_AGENT_SEARCH_PREVIOUS;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentsConnected.COMMAND_AGENTS_CONNECTED;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAssignmentExecute.COMMAND_ASSIGNMENT_EXECUTE;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAssignmentExecutionDelete.COMMAND_ASSIGNMENT_EXECUTION_DELETE;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAssignmentExecutionSearchBegin.COMMAND_ASSIGNMENT_EXECUTION_SEARCH_BEGIN;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAssignmentExecutionSearchNext.COMMAND_ASSIGNMENT_EXECUTION_SEARCH_NEXT;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAssignmentExecutionSearchPrevious.COMMAND_ASSIGNMENT_EXECUTION_SEARCH_PREVIOUS;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAssignmentExecutionWorkItems.COMMAND_ASSIGNMENT_EXECUTION_WORK_ITEMS;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAssignmentGet.COMMAND_ASSIGNMENT_GET;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAssignmentPut.COMMAND_ASSIGNMENT_PUT;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAssignmentSearchBegin.COMMAND_ASSIGNMENT_SEARCH_BEGIN;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAssignmentSearchNext.COMMAND_ASSIGNMENT_SEARCH_NEXT;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAssignmentSearchPrevious.COMMAND_ASSIGNMENT_SEARCH_PREVIOUS;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAuditSearchBegin.COMMAND_AUDIT_SEARCH_BEGIN;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAuditSearchNext.COMMAND_AUDIT_SEARCH_NEXT;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAuditSearchPrevious.COMMAND_AUDIT_SEARCH_PREVIOUS;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandDisconnect.COMMAND_DISCONNECT;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandLogin.COMMAND_LOGIN;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandPlanDelete.COMMAND_PLAN_DELETE;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandPlanGet.COMMAND_PLAN_GET;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandPlanPut.COMMAND_PLAN_PUT;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandPlanSearchBegin.COMMAND_PLAN_SEARCH_BEGIN;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandPlanSearchNext.COMMAND_PLAN_SEARCH_NEXT;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandPlanSearchPrevious.COMMAND_PLAN_SEARCH_PREVIOUS;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandPlanValidate.COMMAND_PLAN_VALIDATE;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandPublicKeyDelete.COMMAND_PUBLIC_KEY_DELETE;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandPublicKeyGet.COMMAND_PUBLIC_KEY_GET;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandPublicKeyPut.COMMAND_PUBLIC_KEY_PUT;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandPublicKeySearchBegin.COMMAND_PUBLIC_KEY_SEARCH_BEGIN;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandPublicKeySearchNext.COMMAND_PUBLIC_KEY_SEARCH_NEXT;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandPublicKeySearchPrevious.COMMAND_PUBLIC_KEY_SEARCH_PREVIOUS;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandRepositoryGet.COMMAND_REPOSITORY_GET;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandRepositoryPublicKeyAssign.COMMAND_REPOSITORY_PUBLIC_KEY_ASSIGN;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandRepositoryPublicKeyUnassign.COMMAND_REPOSITORY_PUBLIC_KEY_UNASSIGN;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandRepositoryPublicKeysAssigned.COMMAND_REPOSITORY_PUBLIC_KEYS_ASSIGNED;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandRepositoryPut.COMMAND_REPOSITORY_PUT;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandRepositorySearchBegin.COMMAND_REPOSITORY_SEARCH_BEGIN;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandRepositorySearchNext.COMMAND_REPOSITORY_SEARCH_NEXT;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandRepositorySearchPrevious.COMMAND_REPOSITORY_SEARCH_PREVIOUS;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandSCMProvidersSupported.COMMAND_SCM_PROVIDERS_SUPPORTED;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandSelf.COMMAND_SELF;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandToolExecutionDescriptionGet.COMMAND_TOOL_EXECUTION_DESCRIPTION_GET;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandToolExecutionDescriptionPut.COMMAND_TOOL_EXECUTION_DESCRIPTION_PUT;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandToolExecutionDescriptionSearchBegin.COMMAND_TOOL_EXECUTION_DESCRIPTION_SEARCH_BEGIN;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandToolExecutionDescriptionSearchNext.COMMAND_TOOL_EXECUTION_DESCRIPTION_SEARCH_NEXT;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandToolExecutionDescriptionSearchPrevious.COMMAND_TOOL_EXECUTION_DESCRIPTION_SEARCH_PREVIOUS;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandToolExecutionDescriptionValidate.COMMAND_TOOL_EXECUTION_DESCRIPTION_VALIDATE;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandUserRolesAssign.COMMAND_USER_ROLES_ASSIGN;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandUserRolesGet.COMMAND_USER_ROLES_GET;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandUserRolesRevoke.COMMAND_USER_ROLES_REVOKE;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandUserSearchBegin.COMMAND_USER_SEARCH_BEGIN;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandUserSearchNext.COMMAND_USER_SEARCH_NEXT;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandUserSearchPrevious.COMMAND_USER_SEARCH_PREVIOUS;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandUsersConnected.COMMAND_USERS_CONNECTED;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseAgentGet.RESPONSE_AGENT_GET;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseAgentLabelGet.RESPONSE_AGENT_LABEL_GET;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseAgentLabelSearch.RESPONSE_AGENT_LABEL_SEARCH;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseAgentSearch.RESPONSE_AGENT_SEARCH;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseAgentsConnected.RESPONSE_AGENTS_CONNECTED;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseAssignmentExecutionSearch.RESPONSE_ASSIGNMENT_EXECUTION_SEARCH;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseAssignmentExecutionWorkItems.RESPONSE_ASSIGNMENT_EXECUTION_WORK_ITEMS;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseAssignmentGet.RESPONSE_ASSIGNMENT_GET;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseAssignmentSearch.RESPONSE_ASSIGNMENT_SEARCH;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseAuditSearch.RESPONSE_AUDIT_SEARCH;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseError.RESPONSE_ERROR;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseOK.RESPONSE_OK;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponsePlanGet.RESPONSE_PLAN_GET;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponsePlanSearch.RESPONSE_PLAN_SEARCH;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponsePlanValidate.RESPONSE_PLAN_VALIDATE;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponsePublicKeyGet.RESPONSE_PUBLIC_KEY_GET;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponsePublicKeySearch.RESPONSE_PUBLIC_KEY_SEARCH;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseRepositoryGet.RESPONSE_REPOSITORY_GET;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseRepositoryPublicKeysAssigned.RESPONSE_REPOSITORY_PUBLIC_KEYS_ASSIGNED;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseRepositorySearch.RESPONSE_REPOSITORY_SEARCH;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseSCMProvidersSupported.RESPONSE_SCM_PROVIDERS_SUPPORTED;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseSelf.RESPONSE_SELF;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseToolExecutionDescriptionGet.RESPONSE_TOOL_EXECUTION_DESCRIPTION_GET;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseToolExecutionDescriptionSearch.RESPONSE_TOOL_EXECUTION_DESCRIPTION_SEARCH;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseToolExecutionDescriptionValidate.RESPONSE_TOOL_EXECUTION_DESCRIPTION_VALIDATE;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseUserRolesGet.RESPONSE_USER_ROLES_GET;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseUserSearch.RESPONSE_USER_SEARCH;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseUsersConnected.RESPONSE_USERS_CONNECTED;

/**
 * Functions to translate between the core command set and the Agent v1
 * Cedarbridge encoding command set.
 */

public final class NPU1Validation
  implements NPProtocolMessageValidatorType<NPUMessageType, ProtocolNPUv1Type>
{
  /**
   * Functions to translate between the core command set and the Agent v1
   * Cedarbridge encoding command set.
   */

  public NPU1Validation()
  {

  }

  @Override
  public ProtocolNPUv1Type convertToWire(
    final NPUMessageType message)
    throws NPProtocolException
  {
    if (message instanceof final NPUCommandType<?> command) {
      return toWireCommand(command);
    }
    if (message instanceof final NPUResponseType response) {
      return toWireResponse(response);
    }
    if (message instanceof final NPUEventType event) {
      return toWireEvent(event);
    }
    throw new IllegalStateException();
  }

  private static ProtocolNPUv1Type toWireEvent(
    final NPUEventType event)
  {
    throw new IllegalStateException();
  }

  private static ProtocolNPUv1Type toWireResponse(
    final NPUResponseType response)
  {
    if (response instanceof final NPUResponseOK r) {
      return RESPONSE_OK.convertToWire(r);
    }
    if (response instanceof final NPUResponseError r) {
      return RESPONSE_ERROR.convertToWire(r);
    }
    if (response instanceof final NPUResponseRepositoryGet r) {
      return RESPONSE_REPOSITORY_GET.convertToWire(r);
    }
    if (response instanceof final NPUResponseRepositorySearch r) {
      return RESPONSE_REPOSITORY_SEARCH.convertToWire(r);
    }
    if (response instanceof final NPUResponseUserRolesGet r) {
      return RESPONSE_USER_ROLES_GET.convertToWire(r);
    }
    if (response instanceof final NPUResponseAgentLabelGet r) {
      return RESPONSE_AGENT_LABEL_GET.convertToWire(r);
    }
    if (response instanceof final NPUResponseAgentLabelSearch r) {
      return RESPONSE_AGENT_LABEL_SEARCH.convertToWire(r);
    }
    if (response instanceof final NPUResponseToolExecutionDescriptionValidate r) {
      return RESPONSE_TOOL_EXECUTION_DESCRIPTION_VALIDATE.convertToWire(r);
    }
    if (response instanceof final NPUResponseToolExecutionDescriptionGet r) {
      return RESPONSE_TOOL_EXECUTION_DESCRIPTION_GET.convertToWire(r);
    }
    if (response instanceof final NPUResponseToolExecutionDescriptionSearch r) {
      return RESPONSE_TOOL_EXECUTION_DESCRIPTION_SEARCH.convertToWire(r);
    }
    if (response instanceof final NPUResponsePlanValidate r) {
      return RESPONSE_PLAN_VALIDATE.convertToWire(r);
    }
    if (response instanceof final NPUResponsePlanGet r) {
      return RESPONSE_PLAN_GET.convertToWire(r);
    }
    if (response instanceof final NPUResponsePlanSearch r) {
      return RESPONSE_PLAN_SEARCH.convertToWire(r);
    }
    if (response instanceof final NPUResponseAgentGet r) {
      return RESPONSE_AGENT_GET.convertToWire(r);
    }
    if (response instanceof final NPUResponseAgentsConnected r) {
      return RESPONSE_AGENTS_CONNECTED.convertToWire(r);
    }
    if (response instanceof final NPUResponseUsersConnected r) {
      return RESPONSE_USERS_CONNECTED.convertToWire(r);
    }
    if (response instanceof final NPUResponseAgentSearch r) {
      return RESPONSE_AGENT_SEARCH.convertToWire(r);
    }
    if (response instanceof final NPUResponseAssignmentGet r) {
      return RESPONSE_ASSIGNMENT_GET.convertToWire(r);
    }
    if (response instanceof final NPUResponseAssignmentSearch r) {
      return RESPONSE_ASSIGNMENT_SEARCH.convertToWire(r);
    }
    if (response instanceof final NPUResponseAssignmentExecutionSearch r) {
      return RESPONSE_ASSIGNMENT_EXECUTION_SEARCH.convertToWire(r);
    }
    if (response instanceof final NPUResponseAssignmentExecutionWorkItems r) {
      return RESPONSE_ASSIGNMENT_EXECUTION_WORK_ITEMS.convertToWire(r);
    }
    if (response instanceof final NPUResponsePublicKeyGet r) {
      return RESPONSE_PUBLIC_KEY_GET.convertToWire(r);
    }
    if (response instanceof final NPUResponsePublicKeySearch r) {
      return RESPONSE_PUBLIC_KEY_SEARCH.convertToWire(r);
    }
    if (response instanceof final NPUResponseRepositoryPublicKeysAssigned r) {
      return RESPONSE_REPOSITORY_PUBLIC_KEYS_ASSIGNED.convertToWire(r);
    }
    if (response instanceof final NPUResponseAuditSearch r) {
      return RESPONSE_AUDIT_SEARCH.convertToWire(r);
    }
    if (response instanceof final NPUResponseSCMProvidersSupported r) {
      return RESPONSE_SCM_PROVIDERS_SUPPORTED.convertToWire(r);
    }
    if (response instanceof final NPUResponseSelf r) {
      return RESPONSE_SELF.convertToWire(r);
    }
    if (response instanceof final NPUResponseUserSearch r) {
      return RESPONSE_USER_SEARCH.convertToWire(r);
    }

    throw new IllegalStateException("Unrecognized response: " + response);
  }

  private static ProtocolNPUv1Type toWireCommand(
    final NPUCommandType<?> command)
    throws NPProtocolException
  {
    if (command instanceof final NPUCommandLogin c) {
      return COMMAND_LOGIN.convertToWire(c);
    }
    if (command instanceof final NPUCommandDisconnect c) {
      return COMMAND_DISCONNECT.convertToWire(c);
    }

    if (command instanceof final NPUCommandRepositoryPut c) {
      return COMMAND_REPOSITORY_PUT.convertToWire(c);
    }
    if (command instanceof final NPUCommandRepositoryGet c) {
      return COMMAND_REPOSITORY_GET.convertToWire(c);
    }
    if (command instanceof final NPUCommandRepositorySearchBegin c) {
      return COMMAND_REPOSITORY_SEARCH_BEGIN.convertToWire(c);
    }
    if (command instanceof final NPUCommandRepositorySearchNext c) {
      return COMMAND_REPOSITORY_SEARCH_NEXT.convertToWire(c);
    }
    if (command instanceof final NPUCommandRepositorySearchPrevious c) {
      return COMMAND_REPOSITORY_SEARCH_PREVIOUS.convertToWire(c);
    }
    if (command instanceof final NPUCommandRepositoryPublicKeyAssign c) {
      return COMMAND_REPOSITORY_PUBLIC_KEY_ASSIGN.convertToWire(c);
    }
    if (command instanceof final NPUCommandRepositoryPublicKeyUnassign c) {
      return COMMAND_REPOSITORY_PUBLIC_KEY_UNASSIGN.convertToWire(c);
    }
    if (command instanceof final NPUCommandRepositoryPublicKeysAssigned c) {
      return COMMAND_REPOSITORY_PUBLIC_KEYS_ASSIGNED.convertToWire(c);
    }

    if (command instanceof final NPUCommandPublicKeyPut c) {
      return COMMAND_PUBLIC_KEY_PUT.convertToWire(c);
    }
    if (command instanceof final NPUCommandPublicKeyGet c) {
      return COMMAND_PUBLIC_KEY_GET.convertToWire(c);
    }
    if (command instanceof final NPUCommandPublicKeySearchBegin c) {
      return COMMAND_PUBLIC_KEY_SEARCH_BEGIN.convertToWire(c);
    }
    if (command instanceof final NPUCommandPublicKeySearchNext c) {
      return COMMAND_PUBLIC_KEY_SEARCH_NEXT.convertToWire(c);
    }
    if (command instanceof final NPUCommandPublicKeySearchPrevious c) {
      return COMMAND_PUBLIC_KEY_SEARCH_PREVIOUS.convertToWire(c);
    }
    if (command instanceof final NPUCommandPublicKeyDelete c) {
      return COMMAND_PUBLIC_KEY_DELETE.convertToWire(c);
    }

    if (command instanceof final NPUCommandUsersConnected c) {
      return COMMAND_USERS_CONNECTED.convertToWire(c);
    }
    if (command instanceof final NPUCommandUserRolesAssign c) {
      return COMMAND_USER_ROLES_ASSIGN.convertToWire(c);
    }
    if (command instanceof final NPUCommandUserRolesRevoke c) {
      return COMMAND_USER_ROLES_REVOKE.convertToWire(c);
    }
    if (command instanceof final NPUCommandUserRolesGet c) {
      return COMMAND_USER_ROLES_GET.convertToWire(c);
    }

    if (command instanceof final NPUCommandAgentLabelPut c) {
      return COMMAND_AGENT_LABEL_PUT.convertToWire(c);
    }
    if (command instanceof final NPUCommandAgentLabelGet c) {
      return COMMAND_AGENT_LABEL_GET.convertToWire(c);
    }
    if (command instanceof final NPUCommandAgentLabelSearchBegin c) {
      return COMMAND_AGENT_LABEL_SEARCH_BEGIN.convertToWire(c);
    }
    if (command instanceof final NPUCommandAgentLabelSearchNext c) {
      return COMMAND_AGENT_LABEL_SEARCH_NEXT.convertToWire(c);
    }
    if (command instanceof final NPUCommandAgentLabelSearchPrevious c) {
      return COMMAND_AGENT_LABEL_SEARCH_PREVIOUS.convertToWire(c);
    }
    if (command instanceof final NPUCommandAgentLabelDelete c) {
      return COMMAND_AGENT_LABEL_DELETE.convertToWire(c);
    }

    if (command instanceof final NPUCommandToolExecutionDescriptionPut c) {
      return COMMAND_TOOL_EXECUTION_DESCRIPTION_PUT.convertToWire(c);
    }
    if (command instanceof final NPUCommandToolExecutionDescriptionValidate c) {
      return COMMAND_TOOL_EXECUTION_DESCRIPTION_VALIDATE.convertToWire(c);
    }
    if (command instanceof final NPUCommandToolExecutionDescriptionGet c) {
      return COMMAND_TOOL_EXECUTION_DESCRIPTION_GET.convertToWire(c);
    }
    if (command instanceof final NPUCommandToolExecutionDescriptionSearchBegin c) {
      return COMMAND_TOOL_EXECUTION_DESCRIPTION_SEARCH_BEGIN.convertToWire(c);
    }
    if (command instanceof final NPUCommandToolExecutionDescriptionSearchNext c) {
      return COMMAND_TOOL_EXECUTION_DESCRIPTION_SEARCH_NEXT.convertToWire(c);
    }
    if (command instanceof final NPUCommandToolExecutionDescriptionSearchPrevious c) {
      return COMMAND_TOOL_EXECUTION_DESCRIPTION_SEARCH_PREVIOUS.convertToWire(c);
    }

    if (command instanceof final NPUCommandPlanPut c) {
      return COMMAND_PLAN_PUT.convertToWire(c);
    }
    if (command instanceof final NPUCommandPlanValidate c) {
      return COMMAND_PLAN_VALIDATE.convertToWire(c);
    }
    if (command instanceof final NPUCommandPlanGet c) {
      return COMMAND_PLAN_GET.convertToWire(c);
    }
    if (command instanceof final NPUCommandPlanSearchBegin c) {
      return COMMAND_PLAN_SEARCH_BEGIN.convertToWire(c);
    }
    if (command instanceof final NPUCommandPlanSearchNext c) {
      return COMMAND_PLAN_SEARCH_NEXT.convertToWire(c);
    }
    if (command instanceof final NPUCommandPlanSearchPrevious c) {
      return COMMAND_PLAN_SEARCH_PREVIOUS.convertToWire(c);
    }
    if (command instanceof final NPUCommandPlanDelete c) {
      return COMMAND_PLAN_DELETE.convertToWire(c);
    }

    if (command instanceof final NPUCommandAgentPut c) {
      return COMMAND_AGENT_PUT.convertToWire(c);
    }
    if (command instanceof final NPUCommandAgentGet c) {
      return COMMAND_AGENT_GET.convertToWire(c);
    }
    if (command instanceof final NPUCommandAgentsConnected c) {
      return COMMAND_AGENTS_CONNECTED.convertToWire(c);
    }
    if (command instanceof final NPUCommandAgentSearchBegin c) {
      return COMMAND_AGENT_SEARCH_BEGIN.convertToWire(c);
    }
    if (command instanceof final NPUCommandAgentSearchNext c) {
      return COMMAND_AGENT_SEARCH_NEXT.convertToWire(c);
    }
    if (command instanceof final NPUCommandAgentSearchPrevious c) {
      return COMMAND_AGENT_SEARCH_PREVIOUS.convertToWire(c);
    }

    if (command instanceof final NPUCommandAssignmentPut c) {
      return COMMAND_ASSIGNMENT_PUT.convertToWire(c);
    }
    if (command instanceof final NPUCommandAssignmentGet c) {
      return COMMAND_ASSIGNMENT_GET.convertToWire(c);
    }
    if (command instanceof final NPUCommandAssignmentSearchBegin c) {
      return COMMAND_ASSIGNMENT_SEARCH_BEGIN.convertToWire(c);
    }
    if (command instanceof final NPUCommandAssignmentSearchNext c) {
      return COMMAND_ASSIGNMENT_SEARCH_NEXT.convertToWire(c);
    }
    if (command instanceof final NPUCommandAssignmentSearchPrevious c) {
      return COMMAND_ASSIGNMENT_SEARCH_PREVIOUS.convertToWire(c);
    }
    if (command instanceof final NPUCommandAssignmentExecute c) {
      return COMMAND_ASSIGNMENT_EXECUTE.convertToWire(c);
    }
    if (command instanceof final NPUCommandAssignmentExecutionDelete c) {
      return COMMAND_ASSIGNMENT_EXECUTION_DELETE.convertToWire(c);
    }
    if (command instanceof final NPUCommandAssignmentExecutionSearchBegin c) {
      return COMMAND_ASSIGNMENT_EXECUTION_SEARCH_BEGIN.convertToWire(c);
    }
    if (command instanceof final NPUCommandAssignmentExecutionSearchNext c) {
      return COMMAND_ASSIGNMENT_EXECUTION_SEARCH_NEXT.convertToWire(c);
    }
    if (command instanceof final NPUCommandAssignmentExecutionSearchPrevious c) {
      return COMMAND_ASSIGNMENT_EXECUTION_SEARCH_PREVIOUS.convertToWire(c);
    }
    if (command instanceof final NPUCommandAssignmentExecutionWorkItems c) {
      return COMMAND_ASSIGNMENT_EXECUTION_WORK_ITEMS.convertToWire(c);
    }

    if (command instanceof final NPUCommandAuditSearchBegin c) {
      return COMMAND_AUDIT_SEARCH_BEGIN.convertToWire(c);
    }
    if (command instanceof final NPUCommandAuditSearchNext c) {
      return COMMAND_AUDIT_SEARCH_NEXT.convertToWire(c);
    }
    if (command instanceof final NPUCommandAuditSearchPrevious c) {
      return COMMAND_AUDIT_SEARCH_PREVIOUS.convertToWire(c);
    }

    if (command instanceof final NPUCommandUserSearchBegin c) {
      return COMMAND_USER_SEARCH_BEGIN.convertToWire(c);
    }
    if (command instanceof final NPUCommandUserSearchNext c) {
      return COMMAND_USER_SEARCH_NEXT.convertToWire(c);
    }
    if (command instanceof final NPUCommandUserSearchPrevious c) {
      return COMMAND_USER_SEARCH_PREVIOUS.convertToWire(c);
    }

    if (command instanceof final NPUCommandSCMProvidersSupported c) {
      return COMMAND_SCM_PROVIDERS_SUPPORTED.convertToWire(c);
    }
    if (command instanceof final NPUCommandSelf c) {
      return COMMAND_SELF.convertToWire(c);
    }

    throw new IllegalStateException("Unrecognized command: " + command);
  }

  @Override
  public NPUMessageType convertFromWire(
    final ProtocolNPUv1Type message)
    throws NPProtocolException
  {
    if (message instanceof final NPU1CommandLogin c) {
      return COMMAND_LOGIN.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandDisconnect c) {
      return COMMAND_DISCONNECT.convertFromWire(c);
    }

    if (message instanceof final NPU1CommandUsersConnected c) {
      return COMMAND_USERS_CONNECTED.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandUserRolesAssign c) {
      return COMMAND_USER_ROLES_ASSIGN.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandUserRolesRevoke c) {
      return COMMAND_USER_ROLES_REVOKE.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandUserRolesGet c) {
      return COMMAND_USER_ROLES_GET.convertFromWire(c);
    }

    if (message instanceof final NPU1CommandRepositoryPut c) {
      return COMMAND_REPOSITORY_PUT.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandRepositoryGet c) {
      return COMMAND_REPOSITORY_GET.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandRepositorySearchBegin c) {
      return COMMAND_REPOSITORY_SEARCH_BEGIN.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandRepositorySearchNext c) {
      return COMMAND_REPOSITORY_SEARCH_NEXT.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandRepositorySearchPrevious c) {
      return COMMAND_REPOSITORY_SEARCH_PREVIOUS.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandRepositoryPublicKeyAssign c) {
      return COMMAND_REPOSITORY_PUBLIC_KEY_ASSIGN.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandRepositoryPublicKeyUnassign c) {
      return COMMAND_REPOSITORY_PUBLIC_KEY_UNASSIGN.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandRepositoryPublicKeysAssigned c) {
      return COMMAND_REPOSITORY_PUBLIC_KEYS_ASSIGNED.convertFromWire(c);
    }

    if (message instanceof final NPU1CommandPublicKeyPut c) {
      return COMMAND_PUBLIC_KEY_PUT.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandPublicKeyGet c) {
      return COMMAND_PUBLIC_KEY_GET.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandPublicKeySearchBegin c) {
      return COMMAND_PUBLIC_KEY_SEARCH_BEGIN.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandPublicKeySearchNext c) {
      return COMMAND_PUBLIC_KEY_SEARCH_NEXT.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandPublicKeySearchPrevious c) {
      return COMMAND_PUBLIC_KEY_SEARCH_PREVIOUS.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandPublicKeyDelete c) {
      return COMMAND_PUBLIC_KEY_DELETE.convertFromWire(c);
    }

    if (message instanceof final NPU1CommandAgentLabelPut c) {
      return COMMAND_AGENT_LABEL_PUT.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandAgentLabelGet c) {
      return COMMAND_AGENT_LABEL_GET.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandAgentLabelSearchBegin c) {
      return COMMAND_AGENT_LABEL_SEARCH_BEGIN.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandAgentLabelSearchNext c) {
      return COMMAND_AGENT_LABEL_SEARCH_NEXT.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandAgentLabelSearchPrevious c) {
      return COMMAND_AGENT_LABEL_SEARCH_PREVIOUS.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandAgentLabelDelete c) {
      return COMMAND_AGENT_LABEL_DELETE.convertFromWire(c);
    }

    if (message instanceof final NPU1CommandToolExecutionDescriptionPut c) {
      return COMMAND_TOOL_EXECUTION_DESCRIPTION_PUT.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandToolExecutionDescriptionValidate c) {
      return COMMAND_TOOL_EXECUTION_DESCRIPTION_VALIDATE.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandToolExecutionDescriptionGet c) {
      return COMMAND_TOOL_EXECUTION_DESCRIPTION_GET.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandToolExecutionDescriptionSearchBegin c) {
      return COMMAND_TOOL_EXECUTION_DESCRIPTION_SEARCH_BEGIN.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandToolExecutionDescriptionSearchNext c) {
      return COMMAND_TOOL_EXECUTION_DESCRIPTION_SEARCH_NEXT.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandToolExecutionDescriptionSearchPrevious c) {
      return COMMAND_TOOL_EXECUTION_DESCRIPTION_SEARCH_PREVIOUS.convertFromWire(c);
    }

    if (message instanceof final NPU1CommandPlanPut c) {
      return COMMAND_PLAN_PUT.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandPlanValidate c) {
      return COMMAND_PLAN_VALIDATE.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandPlanGet c) {
      return COMMAND_PLAN_GET.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandPlanSearchBegin c) {
      return COMMAND_PLAN_SEARCH_BEGIN.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandPlanSearchNext c) {
      return COMMAND_PLAN_SEARCH_NEXT.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandPlanSearchPrevious c) {
      return COMMAND_PLAN_SEARCH_PREVIOUS.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandPlanDelete c) {
      return COMMAND_PLAN_DELETE.convertFromWire(c);
    }

    if (message instanceof final NPU1CommandAgentPut c) {
      return COMMAND_AGENT_PUT.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandAgentGet c) {
      return COMMAND_AGENT_GET.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandAgentsConnected c) {
      return COMMAND_AGENTS_CONNECTED.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandAgentSearchBegin c) {
      return COMMAND_AGENT_SEARCH_BEGIN.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandAgentSearchNext c) {
      return COMMAND_AGENT_SEARCH_NEXT.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandAgentSearchPrevious c) {
      return COMMAND_AGENT_SEARCH_PREVIOUS.convertFromWire(c);
    }

    if (message instanceof final NPU1CommandAuditSearchBegin c) {
      return COMMAND_AUDIT_SEARCH_BEGIN.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandAuditSearchNext c) {
      return COMMAND_AUDIT_SEARCH_NEXT.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandAuditSearchPrevious c) {
      return COMMAND_AUDIT_SEARCH_PREVIOUS.convertFromWire(c);
    }

    if (message instanceof final NPU1CommandUserSearchBegin c) {
      return COMMAND_USER_SEARCH_BEGIN.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandUserSearchNext c) {
      return COMMAND_USER_SEARCH_NEXT.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandUserSearchPrevious c) {
      return COMMAND_USER_SEARCH_PREVIOUS.convertFromWire(c);
    }

    if (message instanceof final NPU1CommandAssignmentPut c) {
      return COMMAND_ASSIGNMENT_PUT.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandAssignmentGet c) {
      return COMMAND_ASSIGNMENT_GET.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandAssignmentSearchBegin c) {
      return COMMAND_ASSIGNMENT_SEARCH_BEGIN.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandAssignmentSearchNext c) {
      return COMMAND_ASSIGNMENT_SEARCH_NEXT.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandAssignmentSearchPrevious c) {
      return COMMAND_ASSIGNMENT_SEARCH_PREVIOUS.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandAssignmentExecute c) {
      return COMMAND_ASSIGNMENT_EXECUTE.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandAssignmentExecutionDelete c) {
      return COMMAND_ASSIGNMENT_EXECUTION_DELETE.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandAssignmentExecutionSearchBegin c) {
      return COMMAND_ASSIGNMENT_EXECUTION_SEARCH_BEGIN.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandAssignmentExecutionSearchNext c) {
      return COMMAND_ASSIGNMENT_EXECUTION_SEARCH_NEXT.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandAssignmentExecutionSearchPrevious c) {
      return COMMAND_ASSIGNMENT_EXECUTION_SEARCH_PREVIOUS.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandAssignmentExecutionWorkItems c) {
      return COMMAND_ASSIGNMENT_EXECUTION_WORK_ITEMS.convertFromWire(c);
    }

    if (message instanceof final NPU1CommandSCMProvidersSupported c) {
      return COMMAND_SCM_PROVIDERS_SUPPORTED.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandSelf c) {
      return COMMAND_SELF.convertFromWire(c);
    }

    if (message instanceof final NPU1ResponseError r) {
      return RESPONSE_ERROR.convertFromWire(r);
    }
    if (message instanceof final NPU1ResponseOK r) {
      return RESPONSE_OK.convertFromWire(r);
    }

    if (message instanceof final NPU1ResponseUserRolesGet r) {
      return RESPONSE_USER_ROLES_GET.convertFromWire(r);
    }

    if (message instanceof final NPU1ResponseRepositoryGet r) {
      return RESPONSE_REPOSITORY_GET.convertFromWire(r);
    }
    if (message instanceof final NPU1ResponseRepositorySearch r) {
      return RESPONSE_REPOSITORY_SEARCH.convertFromWire(r);
    }
    if (message instanceof final NPU1ResponseRepositoryPublicKeysAssigned r) {
      return RESPONSE_REPOSITORY_PUBLIC_KEYS_ASSIGNED.convertFromWire(r);
    }

    if (message instanceof final NPU1ResponseAgentLabelGet r) {
      return RESPONSE_AGENT_LABEL_GET.convertFromWire(r);
    }
    if (message instanceof final NPU1ResponseAgentLabelSearch r) {
      return RESPONSE_AGENT_LABEL_SEARCH.convertFromWire(r);
    }

    if (message instanceof final NPU1ResponseToolExecutionDescriptionValidate r) {
      return RESPONSE_TOOL_EXECUTION_DESCRIPTION_VALIDATE.convertFromWire(r);
    }
    if (message instanceof final NPU1ResponseToolExecutionDescriptionGet r) {
      return RESPONSE_TOOL_EXECUTION_DESCRIPTION_GET.convertFromWire(r);
    }
    if (message instanceof final NPU1ResponseToolExecutionDescriptionSearch r) {
      return RESPONSE_TOOL_EXECUTION_DESCRIPTION_SEARCH.convertFromWire(r);
    }

    if (message instanceof final NPU1ResponsePlanValidate r) {
      return RESPONSE_PLAN_VALIDATE.convertFromWire(r);
    }
    if (message instanceof final NPU1ResponsePlanGet r) {
      return RESPONSE_PLAN_GET.convertFromWire(r);
    }
    if (message instanceof final NPU1ResponsePlanSearch r) {
      return RESPONSE_PLAN_SEARCH.convertFromWire(r);
    }

    if (message instanceof final NPU1ResponseAgentGet r) {
      return RESPONSE_AGENT_GET.convertFromWire(r);
    }
    if (message instanceof final NPU1ResponseAgentsConnected r) {
      return RESPONSE_AGENTS_CONNECTED.convertFromWire(r);
    }
    if (message instanceof final NPU1ResponseAgentSearch r) {
      return RESPONSE_AGENT_SEARCH.convertFromWire(r);
    }

    if (message instanceof final NPU1ResponseAuditSearch r) {
      return RESPONSE_AUDIT_SEARCH.convertFromWire(r);
    }

    if (message instanceof final NPU1ResponseUserSearch r) {
      return RESPONSE_USER_SEARCH.convertFromWire(r);
    }

    if (message instanceof final NPU1ResponseAssignmentGet r) {
      return RESPONSE_ASSIGNMENT_GET.convertFromWire(r);
    }
    if (message instanceof final NPU1ResponseAssignmentSearch r) {
      return RESPONSE_ASSIGNMENT_SEARCH.convertFromWire(r);
    }
    if (message instanceof final NPU1ResponseAssignmentExecutionSearch r) {
      return RESPONSE_ASSIGNMENT_EXECUTION_SEARCH.convertFromWire(r);
    }
    if (message instanceof final NPU1ResponseAssignmentExecutionWorkItems r) {
      return RESPONSE_ASSIGNMENT_EXECUTION_WORK_ITEMS.convertFromWire(r);
    }

    if (message instanceof final NPU1ResponsePublicKeyGet r) {
      return RESPONSE_PUBLIC_KEY_GET.convertFromWire(r);
    }
    if (message instanceof final NPU1ResponsePublicKeySearch r) {
      return RESPONSE_PUBLIC_KEY_SEARCH.convertFromWire(r);
    }

    if (message instanceof final NPU1ResponseUsersConnected r) {
      return RESPONSE_USERS_CONNECTED.convertFromWire(r);
    }

    if (message instanceof final NPU1ResponseSCMProvidersSupported r) {
      return RESPONSE_SCM_PROVIDERS_SUPPORTED.convertFromWire(r);
    }
    if (message instanceof final NPU1ResponseSelf r) {
      return RESPONSE_SELF.convertFromWire(r);
    }

    throw new IllegalStateException("Unrecognized message: " + message);
  }
}
