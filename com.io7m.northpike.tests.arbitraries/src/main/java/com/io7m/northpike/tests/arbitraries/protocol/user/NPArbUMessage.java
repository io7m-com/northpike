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


package com.io7m.northpike.tests.arbitraries.protocol.user;

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
import com.io7m.northpike.protocol.user.NPUCommandAssignmentExecute;
import com.io7m.northpike.protocol.user.NPUCommandAssignmentExecutionSearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandAssignmentExecutionSearchNext;
import com.io7m.northpike.protocol.user.NPUCommandAssignmentExecutionSearchPrevious;
import com.io7m.northpike.protocol.user.NPUCommandAssignmentGet;
import com.io7m.northpike.protocol.user.NPUCommandAssignmentPut;
import com.io7m.northpike.protocol.user.NPUCommandAssignmentSearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandAssignmentSearchNext;
import com.io7m.northpike.protocol.user.NPUCommandAssignmentSearchPrevious;
import com.io7m.northpike.protocol.user.NPUCommandDisconnect;
import com.io7m.northpike.protocol.user.NPUCommandLogin;
import com.io7m.northpike.protocol.user.NPUCommandPlanGet;
import com.io7m.northpike.protocol.user.NPUCommandPlanPut;
import com.io7m.northpike.protocol.user.NPUCommandPlanSearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandPlanSearchNext;
import com.io7m.northpike.protocol.user.NPUCommandPlanSearchPrevious;
import com.io7m.northpike.protocol.user.NPUCommandPlanValidate;
import com.io7m.northpike.protocol.user.NPUCommandRepositoryGet;
import com.io7m.northpike.protocol.user.NPUCommandRepositoryPut;
import com.io7m.northpike.protocol.user.NPUCommandRepositorySearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandRepositorySearchNext;
import com.io7m.northpike.protocol.user.NPUCommandRepositorySearchPrevious;
import com.io7m.northpike.protocol.user.NPUCommandRolesAssign;
import com.io7m.northpike.protocol.user.NPUCommandRolesGet;
import com.io7m.northpike.protocol.user.NPUCommandRolesRevoke;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionGet;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionPut;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionSearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionSearchNext;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionSearchPrevious;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionValidate;
import com.io7m.northpike.protocol.user.NPUMessageType;
import com.io7m.northpike.protocol.user.NPUResponseAgentGet;
import com.io7m.northpike.protocol.user.NPUResponseAgentLabelGet;
import com.io7m.northpike.protocol.user.NPUResponseAgentLabelSearch;
import com.io7m.northpike.protocol.user.NPUResponseAgentSearch;
import com.io7m.northpike.protocol.user.NPUResponseAssignmentExecutionSearch;
import com.io7m.northpike.protocol.user.NPUResponseAssignmentGet;
import com.io7m.northpike.protocol.user.NPUResponseAssignmentSearch;
import com.io7m.northpike.protocol.user.NPUResponseError;
import com.io7m.northpike.protocol.user.NPUResponseOK;
import com.io7m.northpike.protocol.user.NPUResponsePlanGet;
import com.io7m.northpike.protocol.user.NPUResponsePlanSearch;
import com.io7m.northpike.protocol.user.NPUResponsePlanValidate;
import com.io7m.northpike.protocol.user.NPUResponseRepositoryGet;
import com.io7m.northpike.protocol.user.NPUResponseRepositorySearch;
import com.io7m.northpike.protocol.user.NPUResponseRolesGet;
import com.io7m.northpike.protocol.user.NPUResponseToolExecutionDescriptionGet;
import com.io7m.northpike.protocol.user.NPUResponseToolExecutionDescriptionSearch;
import com.io7m.northpike.protocol.user.NPUResponseToolExecutionDescriptionValidate;
import com.io7m.northpike.tests.arbitraries.NPArbAbstract;
import net.jqwik.api.Arbitraries;

import java.util.stream.Collectors;
import java.util.stream.Stream;

public final class NPArbUMessage extends NPArbAbstract<NPUMessageType>
{
  public NPArbUMessage()
  {
    super(
      NPUMessageType.class,
      () -> {
        return Arbitraries.oneOf(
          Stream.of(
              NPUCommandAgentGet.class,
              NPUCommandAgentLabelDelete.class,
              NPUCommandAgentLabelGet.class,
              NPUCommandAgentLabelPut.class,
              NPUCommandAgentLabelSearchBegin.class,
              NPUCommandAgentLabelSearchNext.class,
              NPUCommandAgentLabelSearchPrevious.class,
              NPUCommandAgentPut.class,
              NPUCommandAgentSearchBegin.class,
              NPUCommandAgentSearchNext.class,
              NPUCommandAgentSearchPrevious.class,
              NPUCommandAssignmentExecute.class,
              NPUCommandAssignmentExecutionSearchBegin.class,
              NPUCommandAssignmentExecutionSearchNext.class,
              NPUCommandAssignmentExecutionSearchPrevious.class,
              NPUCommandAssignmentGet.class,
              NPUCommandAssignmentPut.class,
              NPUCommandAssignmentSearchBegin.class,
              NPUCommandAssignmentSearchNext.class,
              NPUCommandAssignmentSearchPrevious.class,
              NPUCommandDisconnect.class,
              NPUCommandLogin.class,
              NPUCommandPlanGet.class,
              NPUCommandPlanPut.class,
              NPUCommandPlanSearchBegin.class,
              NPUCommandPlanSearchNext.class,
              NPUCommandPlanSearchPrevious.class,
              NPUCommandPlanValidate.class,
              NPUCommandRepositoryGet.class,
              NPUCommandRepositoryPut.class,
              NPUCommandRepositorySearchBegin.class,
              NPUCommandRepositorySearchNext.class,
              NPUCommandRepositorySearchPrevious.class,
              NPUCommandRolesAssign.class,
              NPUCommandRolesGet.class,
              NPUCommandRolesRevoke.class,
              NPUCommandToolExecutionDescriptionGet.class,
              NPUCommandToolExecutionDescriptionPut.class,
              NPUCommandToolExecutionDescriptionSearchBegin.class,
              NPUCommandToolExecutionDescriptionSearchNext.class,
              NPUCommandToolExecutionDescriptionSearchPrevious.class,
              NPUCommandToolExecutionDescriptionValidate.class,
              NPUResponseAgentGet.class,
              NPUResponseAgentLabelGet.class,
              NPUResponseAgentLabelSearch.class,
              NPUResponseAgentSearch.class,
              NPUResponseAssignmentExecutionSearch.class,
              NPUResponseAssignmentGet.class,
              NPUResponseAssignmentSearch.class,
              NPUResponseError.class,
              NPUResponseOK.class,
              NPUResponsePlanGet.class,
              NPUResponsePlanSearch.class,
              NPUResponsePlanValidate.class,
              NPUResponseRepositoryGet.class,
              NPUResponseRepositorySearch.class,
              NPUResponseRolesGet.class,
              NPUResponseToolExecutionDescriptionGet.class,
              NPUResponseToolExecutionDescriptionSearch.class,
              NPUResponseToolExecutionDescriptionValidate.class
            ).map(Arbitraries::defaultFor)
            .collect(Collectors.toUnmodifiableList())
        );
      }
    );
  }
}
