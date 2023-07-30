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


package com.io7m.northpike.model;

import java.time.OffsetDateTime;
import java.util.Objects;
import java.util.Set;

/**
 * A commit.
 *
 * @param id             The commit ID
 * @param timeCreated    The commit creation time
 * @param timeReceived   The time the commit was received by this server
 * @param author         The commit author
 * @param messageSubject The commit message subject
 * @param messageBody    The commit message body
 * @param branches       The commit branches
 * @param tags           The tags applied to the commit
 */

public record NPCommit(
  NPCommitID id,
  OffsetDateTime timeCreated,
  OffsetDateTime timeReceived,
  NPCommitAuthor author,
  String messageSubject,
  String messageBody,
  Set<String> branches,
  Set<String> tags)
{
  /**
   * A commit.
   *
   * @param id             The commit ID
   * @param timeCreated    The commit creation time
   * @param timeReceived   The time the commit was received by this server
   * @param author         The commit author
   * @param messageSubject The commit message subject
   * @param messageBody    The commit message body
   * @param branches       The commit branches
   * @param tags           The tags applied to the commit
   */

  public NPCommit
  {
    Objects.requireNonNull(id, "id");
    Objects.requireNonNull(timeCreated, "timeCreated");
    Objects.requireNonNull(timeReceived, "timeReceived");
    Objects.requireNonNull(author, "author");
    Objects.requireNonNull(messageSubject, "messageSubject");
    Objects.requireNonNull(messageBody, "messageBody");
    Objects.requireNonNull(branches, "branches");
    Objects.requireNonNull(tags, "tags");
  }

  /**
   * @return A summary of this commit
   */

  public NPCommitSummary summary()
  {
    return new NPCommitSummary(
      this.id,
      this.timeCreated,
      this.timeReceived,
      this.messageSubject
    );
  }
}
