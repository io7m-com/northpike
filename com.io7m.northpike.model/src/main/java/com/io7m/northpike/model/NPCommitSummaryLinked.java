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

import com.io7m.jaffirm.core.Preconditions;

import java.util.Objects;

/**
 * A commit summary with the associated commit link.
 *
 * @param commit The commit summary
 * @param link   The link
 */

public record NPCommitSummaryLinked(
  NPCommitSummary commit,
  NPCommitLink link)
{
  /**
   * A commit summary with the associated commit link.
   *
   * @param commit The commit summary
   * @param link   The link
   */

  public NPCommitSummaryLinked
  {
    Objects.requireNonNull(commit, "commit");
    Objects.requireNonNull(link, "link");

    Preconditions.checkPreconditionV(
      Objects.equals(commit.id(), link.commit()),
      "Commit ID must match link."
    );
  }
}
