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


package com.io7m.northpike.scm_repository.spi;

import com.io7m.northpike.model.NPCommit;
import com.io7m.northpike.model.NPCommitGraph;

import java.util.Objects;
import java.util.Set;

/**
 * A set of commits produced by an SCM.
 *
 * @param commits     The set of commits
 * @param commitGraph The commit graph
 */

public record NPSCMCommitSet(
  Set<NPCommit> commits,
  NPCommitGraph commitGraph)
{
  /**
   * A set of commits produced by an SCM.
   *
   * @param commits     The set of commits
   * @param commitGraph The commit graph
   */

  public NPSCMCommitSet
  {
    Objects.requireNonNull(commits, "commits");
    Objects.requireNonNull(commitGraph, "commitGraph");
  }
}
