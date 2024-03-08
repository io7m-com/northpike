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


package com.io7m.northpike.plans.variables;

import com.io7m.lanark.core.RDottedName;

/**
 * The standard variables exposed in plans.
 */

public final class NPPlanStandardVariables
{
  private static final NPPlanVariableDeclaration<NPPlanVariableString> SCM_COMMIT =
    new NPPlanVariableDeclaration<>(
      NPPlanVariableString.class,
      new RDottedName("com.io7m.northpike.scm.commit"),
      "The unique identifier of the current SCM commit."
    );

  private static final NPPlanVariableDeclaration<NPPlanVariableStringSet> SCM_BRANCHES =
    new NPPlanVariableDeclaration<>(
      NPPlanVariableStringSet.class,
      new RDottedName("com.io7m.northpike.scm.branches"),
      "The branches to which the current SCM commit belongs."
    );

  private static final NPPlanVariableDeclaration<NPPlanVariableStringSet> SCM_TAGS =
    new NPPlanVariableDeclaration<>(
      NPPlanVariableStringSet.class,
      new RDottedName("com.io7m.northpike.scm.tags"),
      "The tags applied to the current SCM commit."
    );

  private static final NPPlanVariableDeclaration<NPPlanVariableString> ARCHIVE_URL =
    new NPPlanVariableDeclaration<>(
      NPPlanVariableString.class,
      new RDottedName("com.io7m.northpike.archive.url"),
      "The URL that will deliver a source archive for the current plan."
    );

  private static final NPPlanVariableDeclaration<NPPlanVariableString> ARCHIVE_CHECKSUM_URL =
    new NPPlanVariableDeclaration<>(
      NPPlanVariableString.class,
      new RDottedName("com.io7m.northpike.archive.checksum_url"),
      "The URL that will deliver a checksum file for the archive sources."
    );

  private NPPlanStandardVariables()
  {

  }

  /**
   * @return The SCM commit that triggered this plan execution
   */

  public static NPPlanVariableDeclaration<NPPlanVariableString> scmCommit()
  {
    return SCM_COMMIT;
  }

  /**
   * @return The SCM branches to which this commit belongs
   */

  public static NPPlanVariableDeclaration<NPPlanVariableStringSet> scmBranches()
  {
    return SCM_BRANCHES;
  }

  /**
   * @return The SCM tags applied to this commit
   */

  public static NPPlanVariableDeclaration<NPPlanVariableStringSet> scmTags()
  {
    return SCM_TAGS;
  }

  /**
   * @return The URL of the source archive for this plan execution
   */

  public static NPPlanVariableDeclaration<NPPlanVariableString> archiveURL()
  {
    return ARCHIVE_URL;
  }

  /**
   * @return The URL of the checksum of the source archive for this plan execution
   */

  public static NPPlanVariableDeclaration<NPPlanVariableString> archiveChecksumURL()
  {
    return ARCHIVE_CHECKSUM_URL;
  }
}
