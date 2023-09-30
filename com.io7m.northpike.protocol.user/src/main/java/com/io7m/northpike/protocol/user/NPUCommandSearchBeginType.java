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


package com.io7m.northpike.protocol.user;

/**
 * The type of commands that begin searches.
 *
 * @param <R> The type of responses
 * @param <T> The type of search parameters
 */

public sealed interface NPUCommandSearchBeginType<R extends NPUResponseType, T>
  extends NPUCommandType<R>
  permits NPUCommandAgentLabelSearchBegin,
  NPUCommandAgentSearchBegin,
  NPUCommandAssignmentExecutionSearchBegin,
  NPUCommandAssignmentSearchBegin,
  NPUCommandAuditSearchBegin,
  NPUCommandPlanSearchBegin,
  NPUCommandPublicKeySearchBegin,
  NPUCommandRepositorySearchBegin,
  NPUCommandToolExecutionDescriptionSearchBegin,
  NPUCommandUserSearchBegin
{
  /**
   * @return The search parameters
   */

  T parameters();
}
