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

import com.io7m.northpike.model.NPCompilationMessage;

import java.util.List;
import java.util.Objects;
import java.util.UUID;

/**
 * A plan validation.
 *
 * @param messageID           The message ID
 * @param correlationID       The command that prompted this response
 * @param compilationMessages The compilation messages
 */

public record NPUResponsePlanValidate(
  UUID messageID,
  UUID correlationID,
  List<NPCompilationMessage> compilationMessages)
  implements NPUResponseType
{
  /**
   * A plan validation.
   *
   * @param messageID           The message ID
   * @param correlationID       The command that prompted this response
   * @param compilationMessages The compilation messages
   */

  public NPUResponsePlanValidate
  {
    Objects.requireNonNull(messageID, "messageID");
    Objects.requireNonNull(correlationID, "correlationID");
    Objects.requireNonNull(compilationMessages, "compilationMessages");
  }

  /**
   * @param allowWarnings {@code true} if warnings are to be allowed
   *
   * @return {@code true} if the server determine that the plan is valid
   */

  public boolean isValid(
    final boolean allowWarnings)
  {
    return this.compilationMessages.stream()
      .noneMatch(m -> {
        return isKindError(m.kind(), allowWarnings);
      });
  }

  private static boolean isKindError(
    final NPCompilationMessage.Kind kind,
    final boolean allowWarnings)
  {
    return switch (kind) {
      case INFO -> false;
      case WARNING -> !allowWarnings;
      case ERROR -> true;
    };
  }
}
