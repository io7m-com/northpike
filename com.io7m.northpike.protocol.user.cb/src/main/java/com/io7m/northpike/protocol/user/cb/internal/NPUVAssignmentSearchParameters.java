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

import com.io7m.cedarbridge.runtime.api.CBString;
import com.io7m.cedarbridge.runtime.api.CBUUID;
import com.io7m.northpike.model.NPRepositoryID;
import com.io7m.northpike.model.assignments.NPAssignmentSearchParameters;
import com.io7m.northpike.model.plans.NPPlanIdentifier;
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1AssignmentSearchParameters;
import com.io7m.northpike.protocol.user.cb.NPU1PlanIdentifier;

import static com.io7m.cedarbridge.runtime.api.CBCore.unsigned32;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVPlanIdentifier.PLAN_IDENTIFIER;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVRepositoryIdentifier.REPOSITORY_IDENTIFIER;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVStrings.STRINGS;

/**
 * A validator.
 */

public enum NPUVAssignmentSearchParameters
  implements NPProtocolMessageValidatorType<NPAssignmentSearchParameters, NPU1AssignmentSearchParameters>
{
  /**
   * A validator.
   */

  ASSIGNMENT_SEARCH_PARAMETERS;

  private static final NPUVComparisonsFuzzy<String, CBString> NAME_VALIDATOR =
    new NPUVComparisonsFuzzy<>(STRINGS);
  private static final NPUVComparisonsExact<NPPlanIdentifier, NPU1PlanIdentifier> PLAN_VALIDATOR =
    new NPUVComparisonsExact<>(PLAN_IDENTIFIER);
  private static final NPUVComparisonsExact<NPRepositoryID, CBUUID> REPOSITORY_VALIDATOR =
    new NPUVComparisonsExact<>(REPOSITORY_IDENTIFIER);

  @Override
  public NPU1AssignmentSearchParameters convertToWire(
    final NPAssignmentSearchParameters message)
    throws NPProtocolException
  {
    return new NPU1AssignmentSearchParameters(
      REPOSITORY_VALIDATOR.convertToWire(message.repositoryId()),
      PLAN_VALIDATOR.convertToWire(message.plan()),
      NAME_VALIDATOR.convertToWire(message.nameQuery()),
      unsigned32(message.pageSize())
    );
  }

  @Override
  public NPAssignmentSearchParameters convertFromWire(
    final NPU1AssignmentSearchParameters message)
    throws NPProtocolException
  {
    return new NPAssignmentSearchParameters(
      REPOSITORY_VALIDATOR.convertFromWire(message.fieldRepositoryId()),
      PLAN_VALIDATOR.convertFromWire(message.fieldPlan()),
      NAME_VALIDATOR.convertFromWire(message.fieldNameQuery()),
      message.fieldPageSize().value()
    );
  }
}
