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
import com.io7m.northpike.protocol.user.NPUCommandAgentDelete;
import com.io7m.northpike.protocol.user.NPUCommandAgentGet;
import com.io7m.northpike.protocol.user.NPUCommandAgentLabelDelete;
import com.io7m.northpike.protocol.user.NPUCommandAgentLabelGet;
import com.io7m.northpike.protocol.user.NPUCommandAgentLabelPut;
import com.io7m.northpike.protocol.user.NPUCommandAgentLabelSearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandAgentLabelSearchNext;
import com.io7m.northpike.protocol.user.NPUCommandAgentLabelSearchPrevious;
import com.io7m.northpike.protocol.user.NPUCommandAgentLoginChallengeAgentCreate;
import com.io7m.northpike.protocol.user.NPUCommandAgentLoginChallengeDelete;
import com.io7m.northpike.protocol.user.NPUCommandAgentLoginChallengeSearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandAgentLoginChallengeSearchNext;
import com.io7m.northpike.protocol.user.NPUCommandAgentLoginChallengeSearchPrevious;
import com.io7m.northpike.protocol.user.NPUCommandAgentPut;
import com.io7m.northpike.protocol.user.NPUCommandAgentSearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandAgentSearchNext;
import com.io7m.northpike.protocol.user.NPUCommandAgentSearchPrevious;
import com.io7m.northpike.protocol.user.NPUCommandAgentWorkItems;
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
import com.io7m.northpike.protocol.user.NPUCommandPlanFormatsSupported;
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
import com.io7m.northpike.protocol.user.NPUCommandToolGet;
import com.io7m.northpike.protocol.user.NPUCommandToolSearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandToolSearchNext;
import com.io7m.northpike.protocol.user.NPUCommandToolSearchPrevious;
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
import com.io7m.northpike.protocol.user.NPUResponseAgentLoginChallengeSearch;
import com.io7m.northpike.protocol.user.NPUResponseAgentSearch;
import com.io7m.northpike.protocol.user.NPUResponseAgentWorkItems;
import com.io7m.northpike.protocol.user.NPUResponseAgentsConnected;
import com.io7m.northpike.protocol.user.NPUResponseAssignmentExecutionSearch;
import com.io7m.northpike.protocol.user.NPUResponseAssignmentExecutionWorkItems;
import com.io7m.northpike.protocol.user.NPUResponseAssignmentGet;
import com.io7m.northpike.protocol.user.NPUResponseAssignmentSearch;
import com.io7m.northpike.protocol.user.NPUResponseAuditSearch;
import com.io7m.northpike.protocol.user.NPUResponseError;
import com.io7m.northpike.protocol.user.NPUResponseOK;
import com.io7m.northpike.protocol.user.NPUResponsePagedType;
import com.io7m.northpike.protocol.user.NPUResponsePlanFormatsSupported;
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
import com.io7m.northpike.protocol.user.NPUResponseToolGet;
import com.io7m.northpike.protocol.user.NPUResponseToolSearch;
import com.io7m.northpike.protocol.user.NPUResponseType;
import com.io7m.northpike.protocol.user.NPUResponseUserRolesGet;
import com.io7m.northpike.protocol.user.NPUResponseUserSearch;
import com.io7m.northpike.protocol.user.NPUResponseUsersConnected;

import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentDelete.COMMAND_AGENT_DELETE;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentGet.COMMAND_AGENT_GET;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentLabelDelete.COMMAND_AGENT_LABEL_DELETE;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentLabelGet.COMMAND_AGENT_LABEL_GET;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentLabelPut.COMMAND_AGENT_LABEL_PUT;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentLabelSearchBegin.COMMAND_AGENT_LABEL_SEARCH_BEGIN;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentLabelSearchNext.COMMAND_AGENT_LABEL_SEARCH_NEXT;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentLabelSearchPrevious.COMMAND_AGENT_LABEL_SEARCH_PREVIOUS;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentLoginChallengeAgentCreate.COMMAND_AGENT_LOGIN_CHALLENGE_AGENT_CREATE;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentLoginChallengeDelete.COMMAND_AGENT_LOGIN_CHALLENGE_DELETE;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentLoginChallengeSearchBegin.COMMAND_AGENT_LOGIN_CHALLENGE_SEARCH_BEGIN;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentLoginChallengeSearchNext.COMMAND_AGENT_LOGIN_CHALLENGE_SEARCH_NEXT;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentLoginChallengeSearchPrevious.COMMAND_AGENT_LOGIN_CHALLENGE_SEARCH_PREVIOUS;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentPut.COMMAND_AGENT_PUT;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentSearchBegin.COMMAND_AGENT_SEARCH_BEGIN;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentSearchNext.COMMAND_AGENT_SEARCH_NEXT;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentSearchPrevious.COMMAND_AGENT_SEARCH_PREVIOUS;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentWorkItems.COMMAND_AGENT_WORK_ITEMS;
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
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandPlanFormatsSupported.COMMAND_PLAN_FORMATS_SUPPORTED;
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
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandToolGet.COMMAND_TOOL_GET;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandToolSearchBegin.COMMAND_TOOL_SEARCH_BEGIN;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandToolSearchNext.COMMAND_TOOL_SEARCH_NEXT;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandToolSearchPrevious.COMMAND_TOOL_SEARCH_PREVIOUS;
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
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseAgentLoginChallengeSearch.RESPONSE_AGENT_LOGIN_CHALLENGE_SEARCH;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseAgentSearch.RESPONSE_AGENT_SEARCH;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseAgentWorkItems.RESPONSE_AGENT_WORK_ITEMS;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseAgentsConnected.RESPONSE_AGENTS_CONNECTED;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseAssignmentExecutionSearch.RESPONSE_ASSIGNMENT_EXECUTION_SEARCH;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseAssignmentExecutionWorkItems.RESPONSE_ASSIGNMENT_EXECUTION_WORK_ITEMS;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseAssignmentGet.RESPONSE_ASSIGNMENT_GET;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseAssignmentSearch.RESPONSE_ASSIGNMENT_SEARCH;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseAuditSearch.RESPONSE_AUDIT_SEARCH;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseError.RESPONSE_ERROR;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseOK.RESPONSE_OK;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponsePlanFormatsSupported.RESPONSE_PLAN_FORMATS_SUPPORTED;
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
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseToolGet.RESPONSE_TOOL_GET;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseToolSearch.RESPONSE_TOOL_SEARCH;
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
    return switch (message) {
      case final NPUCommandType<?> command -> toWireCommand(command);
      case final NPUResponseType response -> toWireResponse(response);
      case final NPUEventType event -> toWireEvent(event);
    };
  }

  private static ProtocolNPUv1Type toWireEvent(
    final NPUEventType event)
  {
    throw new IllegalStateException();
  }

  private static ProtocolNPUv1Type toWireResponse(
    final NPUResponseType response)
    throws NPProtocolException
  {
    return switch (response) {
      case final NPUResponseAgentGet r ->
        RESPONSE_AGENT_GET.convertToWire(r);
      case final NPUResponseAgentLabelGet r ->
        RESPONSE_AGENT_LABEL_GET.convertToWire(r);
      case final NPUResponseAgentWorkItems r ->
        RESPONSE_AGENT_WORK_ITEMS.convertToWire(r);
      case final NPUResponseAgentsConnected r ->
        RESPONSE_AGENTS_CONNECTED.convertToWire(r);
      case final NPUResponseAssignmentExecutionWorkItems r ->
        RESPONSE_ASSIGNMENT_EXECUTION_WORK_ITEMS.convertToWire(r);
      case final NPUResponseAssignmentGet r ->
        RESPONSE_ASSIGNMENT_GET.convertToWire(r);
      case final NPUResponseError r ->
        RESPONSE_ERROR.convertToWire(r);
      case final NPUResponseOK r ->
        RESPONSE_OK.convertToWire(r);
      case final NPUResponsePlanGet r ->
        RESPONSE_PLAN_GET.convertToWire(r);
      case final NPUResponsePlanValidate r ->
        RESPONSE_PLAN_VALIDATE.convertToWire(r);
      case final NPUResponsePublicKeyGet r ->
        RESPONSE_PUBLIC_KEY_GET.convertToWire(r);
      case final NPUResponseRepositoryGet r ->
        RESPONSE_REPOSITORY_GET.convertToWire(r);
      case final NPUResponseRepositoryPublicKeysAssigned r ->
        RESPONSE_REPOSITORY_PUBLIC_KEYS_ASSIGNED.convertToWire(r);
      case final NPUResponseSCMProvidersSupported r ->
        RESPONSE_SCM_PROVIDERS_SUPPORTED.convertToWire(r);
      case final NPUResponseSelf r ->
        RESPONSE_SELF.convertToWire(r);
      case final NPUResponseToolExecutionDescriptionGet r ->
        RESPONSE_TOOL_EXECUTION_DESCRIPTION_GET.convertToWire(r);
      case final NPUResponseToolExecutionDescriptionValidate r ->
        RESPONSE_TOOL_EXECUTION_DESCRIPTION_VALIDATE.convertToWire(r);
      case final NPUResponseUserRolesGet r ->
        RESPONSE_USER_ROLES_GET.convertToWire(r);
      case final NPUResponseUsersConnected r ->
        RESPONSE_USERS_CONNECTED.convertToWire(r);
      case final NPUResponsePagedType<?> s -> {
        yield switch (s) {
          case final NPUResponseAgentLabelSearch r ->
            RESPONSE_AGENT_LABEL_SEARCH.convertToWire(r);
          case final NPUResponseAgentSearch r ->
            RESPONSE_AGENT_SEARCH.convertToWire(r);
          case final NPUResponseAssignmentExecutionSearch r ->
            RESPONSE_ASSIGNMENT_EXECUTION_SEARCH.convertToWire(r);
          case final NPUResponseAssignmentSearch r ->
            RESPONSE_ASSIGNMENT_SEARCH.convertToWire(r);
          case final NPUResponseAuditSearch r ->
            RESPONSE_AUDIT_SEARCH.convertToWire(r);
          case final NPUResponsePlanSearch r ->
            RESPONSE_PLAN_SEARCH.convertToWire(r);
          case final NPUResponsePublicKeySearch r ->
            RESPONSE_PUBLIC_KEY_SEARCH.convertToWire(r);
          case final NPUResponseRepositorySearch r ->
            RESPONSE_REPOSITORY_SEARCH.convertToWire(r);
          case final NPUResponseToolExecutionDescriptionSearch r ->
            RESPONSE_TOOL_EXECUTION_DESCRIPTION_SEARCH.convertToWire(r);
          case final NPUResponseUserSearch r ->
            RESPONSE_USER_SEARCH.convertToWire(r);
          case final NPUResponseAgentLoginChallengeSearch r ->
            RESPONSE_AGENT_LOGIN_CHALLENGE_SEARCH.convertToWire(r);
          case final NPUResponseToolSearch r ->
            RESPONSE_TOOL_SEARCH.convertToWire(r);
        };
      }
      case final NPUResponseToolGet r ->
        RESPONSE_TOOL_GET.convertToWire(r);
      case final NPUResponsePlanFormatsSupported r ->
        RESPONSE_PLAN_FORMATS_SUPPORTED.convertToWire(r);
    };
  }

  private static ProtocolNPUv1Type toWireCommand(
    final NPUCommandType<?> command)
    throws NPProtocolException
  {
    return switch (command) {
      case final NPUCommandLogin c ->
        COMMAND_LOGIN.convertToWire(c);
      case final NPUCommandDisconnect c ->
        COMMAND_DISCONNECT.convertToWire(c);
      case final NPUCommandRepositoryPut c ->
        COMMAND_REPOSITORY_PUT.convertToWire(c);
      case final NPUCommandRepositoryGet c ->
        COMMAND_REPOSITORY_GET.convertToWire(c);
      case final NPUCommandRepositorySearchBegin c ->
        COMMAND_REPOSITORY_SEARCH_BEGIN.convertToWire(c);
      case final NPUCommandRepositorySearchNext c ->
        COMMAND_REPOSITORY_SEARCH_NEXT.convertToWire(c);
      case final NPUCommandRepositorySearchPrevious c ->
        COMMAND_REPOSITORY_SEARCH_PREVIOUS.convertToWire(c);
      case final NPUCommandRepositoryPublicKeyAssign c ->
        COMMAND_REPOSITORY_PUBLIC_KEY_ASSIGN.convertToWire(c);
      case final NPUCommandRepositoryPublicKeyUnassign c ->
        COMMAND_REPOSITORY_PUBLIC_KEY_UNASSIGN.convertToWire(c);
      case final NPUCommandRepositoryPublicKeysAssigned c ->
        COMMAND_REPOSITORY_PUBLIC_KEYS_ASSIGNED.convertToWire(c);
      case final NPUCommandPublicKeyPut c ->
        COMMAND_PUBLIC_KEY_PUT.convertToWire(c);
      case final NPUCommandPublicKeyGet c ->
        COMMAND_PUBLIC_KEY_GET.convertToWire(c);
      case final NPUCommandPublicKeySearchBegin c ->
        COMMAND_PUBLIC_KEY_SEARCH_BEGIN.convertToWire(c);
      case final NPUCommandPublicKeySearchNext c ->
        COMMAND_PUBLIC_KEY_SEARCH_NEXT.convertToWire(c);
      case final NPUCommandPublicKeySearchPrevious c ->
        COMMAND_PUBLIC_KEY_SEARCH_PREVIOUS.convertToWire(c);
      case final NPUCommandPublicKeyDelete c ->
        COMMAND_PUBLIC_KEY_DELETE.convertToWire(c);
      case final NPUCommandUsersConnected c ->
        COMMAND_USERS_CONNECTED.convertToWire(c);
      case final NPUCommandUserRolesAssign c ->
        COMMAND_USER_ROLES_ASSIGN.convertToWire(c);
      case final NPUCommandUserRolesRevoke c ->
        COMMAND_USER_ROLES_REVOKE.convertToWire(c);
      case final NPUCommandUserRolesGet c ->
        COMMAND_USER_ROLES_GET.convertToWire(c);
      case final NPUCommandAgentLabelPut c ->
        COMMAND_AGENT_LABEL_PUT.convertToWire(c);
      case final NPUCommandAgentLabelGet c ->
        COMMAND_AGENT_LABEL_GET.convertToWire(c);
      case final NPUCommandAgentLabelSearchBegin c ->
        COMMAND_AGENT_LABEL_SEARCH_BEGIN.convertToWire(c);
      case final NPUCommandAgentLabelSearchNext c ->
        COMMAND_AGENT_LABEL_SEARCH_NEXT.convertToWire(c);
      case final NPUCommandAgentLabelSearchPrevious c ->
        COMMAND_AGENT_LABEL_SEARCH_PREVIOUS.convertToWire(c);
      case final NPUCommandAgentLabelDelete c ->
        COMMAND_AGENT_LABEL_DELETE.convertToWire(c);
      case final NPUCommandToolExecutionDescriptionPut c ->
        COMMAND_TOOL_EXECUTION_DESCRIPTION_PUT.convertToWire(c);
      case final NPUCommandToolExecutionDescriptionValidate c ->
        COMMAND_TOOL_EXECUTION_DESCRIPTION_VALIDATE.convertToWire(c);
      case final NPUCommandToolExecutionDescriptionGet c ->
        COMMAND_TOOL_EXECUTION_DESCRIPTION_GET.convertToWire(c);
      case final NPUCommandToolExecutionDescriptionSearchBegin c ->
        COMMAND_TOOL_EXECUTION_DESCRIPTION_SEARCH_BEGIN.convertToWire(c);
      case final NPUCommandToolExecutionDescriptionSearchNext c ->
        COMMAND_TOOL_EXECUTION_DESCRIPTION_SEARCH_NEXT.convertToWire(c);
      case final NPUCommandToolExecutionDescriptionSearchPrevious c ->
        COMMAND_TOOL_EXECUTION_DESCRIPTION_SEARCH_PREVIOUS.convertToWire(c);
      case final NPUCommandPlanPut c ->
        COMMAND_PLAN_PUT.convertToWire(c);
      case final NPUCommandPlanValidate c ->
        COMMAND_PLAN_VALIDATE.convertToWire(c);
      case final NPUCommandPlanGet c ->
        COMMAND_PLAN_GET.convertToWire(c);
      case final NPUCommandPlanSearchBegin c ->
        COMMAND_PLAN_SEARCH_BEGIN.convertToWire(c);
      case final NPUCommandPlanSearchNext c ->
        COMMAND_PLAN_SEARCH_NEXT.convertToWire(c);
      case final NPUCommandPlanSearchPrevious c ->
        COMMAND_PLAN_SEARCH_PREVIOUS.convertToWire(c);
      case final NPUCommandPlanDelete c ->
        COMMAND_PLAN_DELETE.convertToWire(c);
      case final NPUCommandAgentPut c ->
        COMMAND_AGENT_PUT.convertToWire(c);
      case final NPUCommandAgentDelete c ->
        COMMAND_AGENT_DELETE.convertToWire(c);
      case final NPUCommandAgentGet c ->
        COMMAND_AGENT_GET.convertToWire(c);
      case final NPUCommandAgentsConnected c ->
        COMMAND_AGENTS_CONNECTED.convertToWire(c);
      case final NPUCommandAgentWorkItems c ->
        COMMAND_AGENT_WORK_ITEMS.convertToWire(c);
      case final NPUCommandAgentSearchBegin c ->
        COMMAND_AGENT_SEARCH_BEGIN.convertToWire(c);
      case final NPUCommandAgentSearchNext c ->
        COMMAND_AGENT_SEARCH_NEXT.convertToWire(c);
      case final NPUCommandAgentSearchPrevious c ->
        COMMAND_AGENT_SEARCH_PREVIOUS.convertToWire(c);
      case final NPUCommandAssignmentPut c ->
        COMMAND_ASSIGNMENT_PUT.convertToWire(c);
      case final NPUCommandAssignmentGet c ->
        COMMAND_ASSIGNMENT_GET.convertToWire(c);
      case final NPUCommandAssignmentSearchBegin c ->
        COMMAND_ASSIGNMENT_SEARCH_BEGIN.convertToWire(c);
      case final NPUCommandAssignmentSearchNext c ->
        COMMAND_ASSIGNMENT_SEARCH_NEXT.convertToWire(c);
      case final NPUCommandAssignmentSearchPrevious c ->
        COMMAND_ASSIGNMENT_SEARCH_PREVIOUS.convertToWire(c);
      case final NPUCommandAssignmentExecute c ->
        COMMAND_ASSIGNMENT_EXECUTE.convertToWire(c);
      case final NPUCommandAssignmentExecutionDelete c ->
        COMMAND_ASSIGNMENT_EXECUTION_DELETE.convertToWire(c);
      case final NPUCommandAssignmentExecutionSearchBegin c ->
        COMMAND_ASSIGNMENT_EXECUTION_SEARCH_BEGIN.convertToWire(c);
      case final NPUCommandAssignmentExecutionSearchNext c ->
        COMMAND_ASSIGNMENT_EXECUTION_SEARCH_NEXT.convertToWire(c);
      case final NPUCommandAssignmentExecutionSearchPrevious c ->
        COMMAND_ASSIGNMENT_EXECUTION_SEARCH_PREVIOUS.convertToWire(c);
      case final NPUCommandAssignmentExecutionWorkItems c ->
        COMMAND_ASSIGNMENT_EXECUTION_WORK_ITEMS.convertToWire(c);
      case final NPUCommandAuditSearchBegin c ->
        COMMAND_AUDIT_SEARCH_BEGIN.convertToWire(c);
      case final NPUCommandAuditSearchNext c ->
        COMMAND_AUDIT_SEARCH_NEXT.convertToWire(c);
      case final NPUCommandAuditSearchPrevious c ->
        COMMAND_AUDIT_SEARCH_PREVIOUS.convertToWire(c);
      case final NPUCommandUserSearchBegin c ->
        COMMAND_USER_SEARCH_BEGIN.convertToWire(c);
      case final NPUCommandUserSearchNext c ->
        COMMAND_USER_SEARCH_NEXT.convertToWire(c);
      case final NPUCommandUserSearchPrevious c ->
        COMMAND_USER_SEARCH_PREVIOUS.convertToWire(c);
      case final NPUCommandSCMProvidersSupported c ->
        COMMAND_SCM_PROVIDERS_SUPPORTED.convertToWire(c);
      case final NPUCommandSelf c ->
        COMMAND_SELF.convertToWire(c);
      case final NPUCommandAgentLoginChallengeSearchBegin c ->
        COMMAND_AGENT_LOGIN_CHALLENGE_SEARCH_BEGIN.convertToWire(c);
      case final NPUCommandAgentLoginChallengeSearchNext c ->
        COMMAND_AGENT_LOGIN_CHALLENGE_SEARCH_NEXT.convertToWire(c);
      case final NPUCommandAgentLoginChallengeSearchPrevious c ->
        COMMAND_AGENT_LOGIN_CHALLENGE_SEARCH_PREVIOUS.convertToWire(c);
      case final NPUCommandAgentLoginChallengeDelete c ->
        COMMAND_AGENT_LOGIN_CHALLENGE_DELETE.convertToWire(c);
      case final NPUCommandAgentLoginChallengeAgentCreate c ->
        COMMAND_AGENT_LOGIN_CHALLENGE_AGENT_CREATE.convertToWire(c);
      case final NPUCommandToolSearchBegin c ->
        COMMAND_TOOL_SEARCH_BEGIN.convertToWire(c);
      case final NPUCommandToolSearchNext c ->
        COMMAND_TOOL_SEARCH_NEXT.convertToWire(c);
      case final NPUCommandToolSearchPrevious c ->
        COMMAND_TOOL_SEARCH_PREVIOUS.convertToWire(c);
      case final NPUCommandToolGet c ->
        COMMAND_TOOL_GET.convertToWire(c);
      case final NPUCommandPlanFormatsSupported c ->
        COMMAND_PLAN_FORMATS_SUPPORTED.convertToWire(c);
    };
  }

  @Override
  public NPUMessageType convertFromWire(
    final ProtocolNPUv1Type message)
    throws NPProtocolException
  {
    return switch (message) {
      case final NPU1CommandLogin c ->
        COMMAND_LOGIN.convertFromWire(c);
      case final NPU1CommandDisconnect c ->
        COMMAND_DISCONNECT.convertFromWire(c);
      case final NPU1CommandUsersConnected c ->
        COMMAND_USERS_CONNECTED.convertFromWire(c);
      case final NPU1CommandUserRolesAssign c ->
        COMMAND_USER_ROLES_ASSIGN.convertFromWire(c);
      case final NPU1CommandUserRolesRevoke c ->
        COMMAND_USER_ROLES_REVOKE.convertFromWire(c);
      case final NPU1CommandUserRolesGet c ->
        COMMAND_USER_ROLES_GET.convertFromWire(c);
      case final NPU1CommandRepositoryPut c ->
        COMMAND_REPOSITORY_PUT.convertFromWire(c);
      case final NPU1CommandRepositoryGet c ->
        COMMAND_REPOSITORY_GET.convertFromWire(c);
      case final NPU1CommandRepositorySearchBegin c ->
        COMMAND_REPOSITORY_SEARCH_BEGIN.convertFromWire(c);
      case final NPU1CommandRepositorySearchNext c ->
        COMMAND_REPOSITORY_SEARCH_NEXT.convertFromWire(c);
      case final NPU1CommandRepositorySearchPrevious c ->
        COMMAND_REPOSITORY_SEARCH_PREVIOUS.convertFromWire(c);
      case final NPU1CommandRepositoryPublicKeyAssign c ->
        COMMAND_REPOSITORY_PUBLIC_KEY_ASSIGN.convertFromWire(c);
      case final NPU1CommandRepositoryPublicKeyUnassign c ->
        COMMAND_REPOSITORY_PUBLIC_KEY_UNASSIGN.convertFromWire(c);
      case final NPU1CommandRepositoryPublicKeysAssigned c ->
        COMMAND_REPOSITORY_PUBLIC_KEYS_ASSIGNED.convertFromWire(c);
      case final NPU1CommandPublicKeyPut c ->
        COMMAND_PUBLIC_KEY_PUT.convertFromWire(c);
      case final NPU1CommandPublicKeyGet c ->
        COMMAND_PUBLIC_KEY_GET.convertFromWire(c);
      case final NPU1CommandPublicKeySearchBegin c ->
        COMMAND_PUBLIC_KEY_SEARCH_BEGIN.convertFromWire(c);
      case final NPU1CommandPublicKeySearchNext c ->
        COMMAND_PUBLIC_KEY_SEARCH_NEXT.convertFromWire(c);
      case final NPU1CommandPublicKeySearchPrevious c ->
        COMMAND_PUBLIC_KEY_SEARCH_PREVIOUS.convertFromWire(c);
      case final NPU1CommandPublicKeyDelete c ->
        COMMAND_PUBLIC_KEY_DELETE.convertFromWire(c);
      case final NPU1CommandAgentLabelPut c ->
        COMMAND_AGENT_LABEL_PUT.convertFromWire(c);
      case final NPU1CommandAgentLabelGet c ->
        COMMAND_AGENT_LABEL_GET.convertFromWire(c);
      case final NPU1CommandAgentLabelSearchBegin c ->
        COMMAND_AGENT_LABEL_SEARCH_BEGIN.convertFromWire(c);
      case final NPU1CommandAgentLabelSearchNext c ->
        COMMAND_AGENT_LABEL_SEARCH_NEXT.convertFromWire(c);
      case final NPU1CommandAgentLabelSearchPrevious c ->
        COMMAND_AGENT_LABEL_SEARCH_PREVIOUS.convertFromWire(c);
      case final NPU1CommandAgentLabelDelete c ->
        COMMAND_AGENT_LABEL_DELETE.convertFromWire(c);
      case final NPU1CommandToolExecutionDescriptionPut c ->
        COMMAND_TOOL_EXECUTION_DESCRIPTION_PUT.convertFromWire(c);
      case final NPU1CommandToolExecutionDescriptionValidate c ->
        COMMAND_TOOL_EXECUTION_DESCRIPTION_VALIDATE.convertFromWire(c);
      case final NPU1CommandToolExecutionDescriptionGet c ->
        COMMAND_TOOL_EXECUTION_DESCRIPTION_GET.convertFromWire(c);
      case final NPU1CommandToolExecutionDescriptionSearchBegin c ->
        COMMAND_TOOL_EXECUTION_DESCRIPTION_SEARCH_BEGIN.convertFromWire(c);
      case final NPU1CommandToolExecutionDescriptionSearchNext c ->
        COMMAND_TOOL_EXECUTION_DESCRIPTION_SEARCH_NEXT.convertFromWire(c);
      case final NPU1CommandToolExecutionDescriptionSearchPrevious c ->
        COMMAND_TOOL_EXECUTION_DESCRIPTION_SEARCH_PREVIOUS.convertFromWire(c);
      case final NPU1CommandPlanPut c ->
        COMMAND_PLAN_PUT.convertFromWire(c);
      case final NPU1CommandPlanValidate c ->
        COMMAND_PLAN_VALIDATE.convertFromWire(c);
      case final NPU1CommandPlanGet c ->
        COMMAND_PLAN_GET.convertFromWire(c);
      case final NPU1CommandPlanSearchBegin c ->
        COMMAND_PLAN_SEARCH_BEGIN.convertFromWire(c);
      case final NPU1CommandPlanSearchNext c ->
        COMMAND_PLAN_SEARCH_NEXT.convertFromWire(c);
      case final NPU1CommandPlanSearchPrevious c ->
        COMMAND_PLAN_SEARCH_PREVIOUS.convertFromWire(c);
      case final NPU1CommandPlanDelete c ->
        COMMAND_PLAN_DELETE.convertFromWire(c);
      case final NPU1CommandAgentPut c ->
        COMMAND_AGENT_PUT.convertFromWire(c);
      case final NPU1CommandAgentGet c ->
        COMMAND_AGENT_GET.convertFromWire(c);
      case final NPU1CommandAgentDelete c ->
        COMMAND_AGENT_DELETE.convertFromWire(c);
      case final NPU1CommandAgentsConnected c ->
        COMMAND_AGENTS_CONNECTED.convertFromWire(c);
      case final NPU1CommandAgentWorkItems c ->
        COMMAND_AGENT_WORK_ITEMS.convertFromWire(c);
      case final NPU1CommandAgentSearchBegin c ->
        COMMAND_AGENT_SEARCH_BEGIN.convertFromWire(c);
      case final NPU1CommandAgentSearchNext c ->
        COMMAND_AGENT_SEARCH_NEXT.convertFromWire(c);
      case final NPU1CommandAgentSearchPrevious c ->
        COMMAND_AGENT_SEARCH_PREVIOUS.convertFromWire(c);
      case final NPU1CommandAuditSearchBegin c ->
        COMMAND_AUDIT_SEARCH_BEGIN.convertFromWire(c);
      case final NPU1CommandAuditSearchNext c ->
        COMMAND_AUDIT_SEARCH_NEXT.convertFromWire(c);
      case final NPU1CommandAuditSearchPrevious c ->
        COMMAND_AUDIT_SEARCH_PREVIOUS.convertFromWire(c);
      case final NPU1CommandUserSearchBegin c ->
        COMMAND_USER_SEARCH_BEGIN.convertFromWire(c);
      case final NPU1CommandUserSearchNext c ->
        COMMAND_USER_SEARCH_NEXT.convertFromWire(c);
      case final NPU1CommandUserSearchPrevious c ->
        COMMAND_USER_SEARCH_PREVIOUS.convertFromWire(c);
      case final NPU1CommandAssignmentPut c ->
        COMMAND_ASSIGNMENT_PUT.convertFromWire(c);
      case final NPU1CommandAssignmentGet c ->
        COMMAND_ASSIGNMENT_GET.convertFromWire(c);
      case final NPU1CommandAssignmentSearchBegin c ->
        COMMAND_ASSIGNMENT_SEARCH_BEGIN.convertFromWire(c);
      case final NPU1CommandAssignmentSearchNext c ->
        COMMAND_ASSIGNMENT_SEARCH_NEXT.convertFromWire(c);
      case final NPU1CommandAssignmentSearchPrevious c ->
        COMMAND_ASSIGNMENT_SEARCH_PREVIOUS.convertFromWire(c);
      case final NPU1CommandAssignmentExecute c ->
        COMMAND_ASSIGNMENT_EXECUTE.convertFromWire(c);
      case final NPU1CommandAssignmentExecutionDelete c ->
        COMMAND_ASSIGNMENT_EXECUTION_DELETE.convertFromWire(c);
      case final NPU1CommandAssignmentExecutionSearchBegin c ->
        COMMAND_ASSIGNMENT_EXECUTION_SEARCH_BEGIN.convertFromWire(c);
      case final NPU1CommandAssignmentExecutionSearchNext c ->
        COMMAND_ASSIGNMENT_EXECUTION_SEARCH_NEXT.convertFromWire(c);
      case final NPU1CommandAssignmentExecutionSearchPrevious c ->
        COMMAND_ASSIGNMENT_EXECUTION_SEARCH_PREVIOUS.convertFromWire(c);
      case final NPU1CommandAssignmentExecutionWorkItems c ->
        COMMAND_ASSIGNMENT_EXECUTION_WORK_ITEMS.convertFromWire(c);
      case final NPU1CommandSCMProvidersSupported c ->
        COMMAND_SCM_PROVIDERS_SUPPORTED.convertFromWire(c);
      case final NPU1CommandSelf c ->
        COMMAND_SELF.convertFromWire(c);
      case final NPU1ResponseError r ->
        RESPONSE_ERROR.convertFromWire(r);
      case final NPU1ResponseOK r ->
        RESPONSE_OK.convertFromWire(r);
      case final NPU1ResponseUserRolesGet r ->
        RESPONSE_USER_ROLES_GET.convertFromWire(r);
      case final NPU1ResponseRepositoryGet r ->
        RESPONSE_REPOSITORY_GET.convertFromWire(r);
      case final NPU1ResponseRepositorySearch r ->
        RESPONSE_REPOSITORY_SEARCH.convertFromWire(r);
      case final NPU1ResponseRepositoryPublicKeysAssigned r ->
        RESPONSE_REPOSITORY_PUBLIC_KEYS_ASSIGNED.convertFromWire(r);
      case final NPU1ResponseAgentLabelGet r ->
        RESPONSE_AGENT_LABEL_GET.convertFromWire(r);
      case final NPU1ResponseAgentLabelSearch r ->
        RESPONSE_AGENT_LABEL_SEARCH.convertFromWire(r);
      case final NPU1ResponseToolExecutionDescriptionValidate r ->
        RESPONSE_TOOL_EXECUTION_DESCRIPTION_VALIDATE.convertFromWire(r);
      case final NPU1ResponseToolExecutionDescriptionGet r ->
        RESPONSE_TOOL_EXECUTION_DESCRIPTION_GET.convertFromWire(r);
      case final NPU1ResponseToolExecutionDescriptionSearch r ->
        RESPONSE_TOOL_EXECUTION_DESCRIPTION_SEARCH.convertFromWire(r);
      case final NPU1ResponsePlanValidate r ->
        RESPONSE_PLAN_VALIDATE.convertFromWire(r);
      case final NPU1ResponsePlanGet r ->
        RESPONSE_PLAN_GET.convertFromWire(r);
      case final NPU1ResponsePlanSearch r ->
        RESPONSE_PLAN_SEARCH.convertFromWire(r);
      case final NPU1ResponseAgentGet r ->
        RESPONSE_AGENT_GET.convertFromWire(r);
      case final NPU1ResponseAgentsConnected r ->
        RESPONSE_AGENTS_CONNECTED.convertFromWire(r);
      case final NPU1ResponseAgentSearch r ->
        RESPONSE_AGENT_SEARCH.convertFromWire(r);
      case final NPU1ResponseAgentWorkItems r ->
        RESPONSE_AGENT_WORK_ITEMS.convertFromWire(r);
      case final NPU1ResponseAuditSearch r ->
        RESPONSE_AUDIT_SEARCH.convertFromWire(r);
      case final NPU1ResponseUserSearch r ->
        RESPONSE_USER_SEARCH.convertFromWire(r);
      case final NPU1ResponseAssignmentGet r ->
        RESPONSE_ASSIGNMENT_GET.convertFromWire(r);
      case final NPU1ResponseAssignmentSearch r ->
        RESPONSE_ASSIGNMENT_SEARCH.convertFromWire(r);
      case final NPU1ResponseAssignmentExecutionSearch r ->
        RESPONSE_ASSIGNMENT_EXECUTION_SEARCH.convertFromWire(r);
      case final NPU1ResponseAssignmentExecutionWorkItems r ->
        RESPONSE_ASSIGNMENT_EXECUTION_WORK_ITEMS.convertFromWire(r);
      case final NPU1ResponsePublicKeyGet r ->
        RESPONSE_PUBLIC_KEY_GET.convertFromWire(r);
      case final NPU1ResponsePublicKeySearch r ->
        RESPONSE_PUBLIC_KEY_SEARCH.convertFromWire(r);
      case final NPU1ResponseUsersConnected r ->
        RESPONSE_USERS_CONNECTED.convertFromWire(r);
      case final NPU1ResponseSCMProvidersSupported r ->
        RESPONSE_SCM_PROVIDERS_SUPPORTED.convertFromWire(r);
      case final NPU1ResponseSelf r ->
        RESPONSE_SELF.convertFromWire(r);
      case final NPU1CommandAgentLoginChallengeSearchBegin c ->
        COMMAND_AGENT_LOGIN_CHALLENGE_SEARCH_BEGIN.convertFromWire(c);
      case final NPU1CommandAgentLoginChallengeSearchNext c ->
        COMMAND_AGENT_LOGIN_CHALLENGE_SEARCH_NEXT.convertFromWire(c);
      case final NPU1CommandAgentLoginChallengeSearchPrevious c ->
        COMMAND_AGENT_LOGIN_CHALLENGE_SEARCH_PREVIOUS.convertFromWire(c);
      case final NPU1ResponseAgentLoginChallengeSearch r ->
        RESPONSE_AGENT_LOGIN_CHALLENGE_SEARCH.convertFromWire(r);
      case final NPU1CommandAgentLoginChallengeDelete c ->
        COMMAND_AGENT_LOGIN_CHALLENGE_DELETE.convertFromWire(c);
      case final NPU1CommandAgentLoginChallengeAgentCreate c ->
        COMMAND_AGENT_LOGIN_CHALLENGE_AGENT_CREATE.convertFromWire(c);
      case final NPU1CommandToolSearchBegin c ->
        COMMAND_TOOL_SEARCH_BEGIN.convertFromWire(c);
      case final NPU1CommandToolSearchNext c ->
        COMMAND_TOOL_SEARCH_NEXT.convertFromWire(c);
      case final NPU1CommandToolSearchPrevious c ->
        COMMAND_TOOL_SEARCH_PREVIOUS.convertFromWire(c);
      case final NPU1ResponseToolSearch c ->
        RESPONSE_TOOL_SEARCH.convertFromWire(c);
      case final NPU1CommandToolGet c ->
        COMMAND_TOOL_GET.convertFromWire(c);
      case final NPU1ResponseToolGet r ->
        RESPONSE_TOOL_GET.convertFromWire(r);
      case final NPU1CommandPlanFormatsSupported r ->
        COMMAND_PLAN_FORMATS_SUPPORTED.convertFromWire(r);
      case final NPU1ResponsePlanFormatsSupported c ->
        RESPONSE_PLAN_FORMATS_SUPPORTED.convertFromWire(c);
    };
  }
}
