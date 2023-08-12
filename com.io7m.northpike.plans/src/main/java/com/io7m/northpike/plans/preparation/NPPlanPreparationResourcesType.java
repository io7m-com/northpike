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


package com.io7m.northpike.plans.preparation;

import com.io7m.northpike.model.NPCommit;
import com.io7m.northpike.model.NPToolExecutionIdentifier;
import com.io7m.northpike.plans.NPPlanException;
import com.io7m.northpike.plans.variables.NPPlanVariables;
import com.io7m.northpike.toolexec.checker.NPTXTypeChecked;

import java.net.URI;
import java.util.Objects;

/**
 * An interface that can be used to fetch resources that are necessary
 * for preparing a plan for execution.
 */

public interface NPPlanPreparationResourcesType
{
  /**
   * Compile a tool execution for the given plan variables.
   *
   * @param execution     The tool execution
   * @param planVariables The plan variables
   *
   * @return A type-checked execution
   *
   * @throws NPPlanException On errors
   */

  NPTXTypeChecked toolCompile(
    NPToolExecutionIdentifier execution,
    NPPlanVariables planVariables)
    throws NPPlanException;

  /**
   * An archive of sources used to execute a plan.
   *
   * @param sources  The URI of the archive of sources
   * @param checksum The URI of the checksum of the archive
   */

  record Archive(
    URI sources,
    URI checksum)
  {
    /**
     * An archive of sources used to execute a plan.
     */

    public Archive
    {
      Objects.requireNonNull(sources, "sources");
      Objects.requireNonNull(checksum, "checksum");
    }
  }

  /**
   * Return a link to the archive for the given commit.
   *
   * @param commit The commit
   *
   * @return A link to the archive
   *
   * @throws NPPlanException On errors
   */

  Archive archiveForCommit(NPCommit commit)
    throws NPPlanException;
}
