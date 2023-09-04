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

package com.io7m.northpike.server.internal.security;

import com.io7m.medrina.api.MActionName;
import com.io7m.medrina.api.MObject;
import com.io7m.medrina.api.MPolicy;
import com.io7m.medrina.api.MPolicyAccess;
import com.io7m.medrina.api.MPolicyEvaluator;
import com.io7m.medrina.api.MPolicyEvaluatorType;
import com.io7m.medrina.api.MRoleName;
import com.io7m.medrina.api.MSubject;
import com.io7m.northpike.model.NPStandardErrorCodes;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.UUID;
import java.util.stream.Collectors;

/**
 * The main API for performing security policy checks.
 */

public final class NPSecurity
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPSecurity.class);

  private static volatile MPolicy POLICY =
    new MPolicy(List.of());

  private static final MPolicyEvaluatorType EVALUATOR =
    MPolicyEvaluator.create();

  private NPSecurity()
  {

  }

  /**
   * Set the currently loaded policy.
   *
   * @param policy The policy
   */

  public static void setPolicy(
    final MPolicy policy)
  {
    POLICY = Objects.requireNonNull(policy, "policy");
  }

  /**
   * Check that a user is allowed to perform an action by the current policy.
   *
   * @param userId     The user ID
   * @param subject    The user
   * @param object     The object upon which the action is being performed
   * @param actionName The action
   *
   * @throws NPSecurityException If the operation is denied
   */

  public static void check(
    final UUID userId,
    final MSubject subject,
    final MObject object,
    final MActionName actionName)
    throws NPSecurityException
  {
    Objects.requireNonNull(userId, "userId");
    Objects.requireNonNull(subject, "subject");
    Objects.requireNonNull(object, "object");
    Objects.requireNonNull(actionName, "actionName");

    final var result =
      EVALUATOR.evaluate(POLICY, subject, object, actionName);

    if (result.accessResult() == MPolicyAccess.ACCESS_DENIED) {
      LOG.warn(
        "{} deny {} {} on {}",
        userId,
        subject.roles()
          .stream()
          .map(MRoleName::value)
          .collect(Collectors.toUnmodifiableSet()),
        actionName.value(),
        object.type().value()
      );

      throw new NPSecurityException(
        "Operation not permitted.",
        NPStandardErrorCodes.errorSecurityPolicyDenied(),
        Map.of(),
        Optional.empty()
      );
    }
  }
}
