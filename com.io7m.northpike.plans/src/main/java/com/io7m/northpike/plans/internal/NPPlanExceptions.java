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


package com.io7m.northpike.plans.internal;

import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.model.NPToolReference;
import com.io7m.northpike.model.NPToolReferenceName;
import com.io7m.northpike.model.plans.NPPlanElementName;
import com.io7m.northpike.model.plans.NPPlanException;
import com.io7m.northpike.strings.NPStringConstants;
import com.io7m.northpike.strings.NPStrings;

import java.util.Map;
import java.util.Optional;

import static com.io7m.northpike.strings.NPStringConstants.ERROR_DUPLICATE;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_NONEXISTENT;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_NO_TOOL_EXECUTION;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_PLAN_CYCLIC;
import static com.io7m.northpike.strings.NPStringConstants.SOURCE;
import static com.io7m.northpike.strings.NPStringConstants.TARGET;
import static com.io7m.northpike.strings.NPStringConstants.TASK;
import static com.io7m.northpike.strings.NPStringConstants.TOOL_REFERENCE;

/**
 * Functions to construct plan exceptions.
 */

public final class NPPlanExceptions
{
  private NPPlanExceptions()
  {

  }

  /**
   * A tool reference was duplicated.
   *
   * @param strings   String resources
   * @param reference The reference
   *
   * @return An exception
   */

  public static NPPlanException errorDuplicateToolReference(
    final NPStrings strings,
    final NPToolReference reference)
  {
    return new NPPlanException(
      strings.format(ERROR_DUPLICATE),
      NPStandardErrorCodes.errorDuplicate(),
      Map.ofEntries(
        Map.entry(
          strings.format(TOOL_REFERENCE),
          reference.referenceName().toString()
        )
      ),
      Optional.empty()
    );
  }

  /**
   * An element was duplicated.
   *
   * @param strings String resources
   * @param name    The name
   * @param kind    The kind
   *
   * @return An exception
   */

  public static NPPlanException errorDuplicateElement(
    final NPStrings strings,
    final NPPlanElementName name,
    final NPStringConstants kind)
  {
    return new NPPlanException(
      strings.format(ERROR_DUPLICATE),
      NPStandardErrorCodes.errorDuplicate(),
      Map.ofEntries(
        Map.entry(
          strings.format(kind),
          name.toString()
        )
      ),
      Optional.empty()
    );
  }

  /**
   * An element cycle was introduced.
   *
   * @param strings String resources
   * @param e       The exception
   * @param source  The source
   * @param target  The target
   *
   * @return An exception
   */

  public static NPPlanException errorCycle(
    final NPStrings strings,
    final Exception e,
    final NPPlanElementName source,
    final NPPlanElementName target)
  {
    return new NPPlanException(
      strings.format(ERROR_PLAN_CYCLIC),
      e,
      NPStandardErrorCodes.errorCyclic(),
      Map.ofEntries(
        Map.entry(
          strings.format(SOURCE),
          source.toString()
        ),
        Map.entry(
          strings.format(TARGET),
          target.toString()
        )
      ),
      Optional.empty()
    );
  }

  /**
   * A tool reference did not exist.
   *
   * @param strings String resources
   * @param name    The name
   *
   * @return An exception
   */

  public static NPPlanException errorNonexistentToolReference(
    final NPStrings strings,
    final NPToolReferenceName name)
  {
    return new NPPlanException(
      strings.format(ERROR_NONEXISTENT),
      NPStandardErrorCodes.errorNonexistent(),
      Map.ofEntries(
        Map.entry(
          strings.format(TOOL_REFERENCE),
          name.toString()
        )
      ),
      Optional.empty()
    );
  }

  /**
   * An element was missing a required tool execution.
   *
   * @param strings String resources
   * @param name    The name
   *
   * @return An exception
   */

  public static NPPlanException errorNoToolExecution(
    final NPStrings strings,
    final NPPlanElementName name)
  {
    return new NPPlanException(
      strings.format(ERROR_NO_TOOL_EXECUTION),
      NPStandardErrorCodes.errorApiMisuse(),
      Map.ofEntries(
        Map.entry(
          strings.format(TASK),
          name.toString()
        )
      ),
      Optional.empty()
    );
  }

  /**
   * An element referred to a nonexistent element.
   *
   * @param strings String resources
   * @param e       The exception
   * @param source  The source
   * @param target  The target
   *
   * @return An exception
   */

  public static NPPlanException errorNonexistentElement(
    final NPStrings strings,
    final Exception e,
    final NPPlanElementName source,
    final NPPlanElementName target)
  {
    return new NPPlanException(
      strings.format(ERROR_NONEXISTENT),
      e,
      NPStandardErrorCodes.errorNonexistent(),
      Map.ofEntries(
        Map.entry(
          strings.format(SOURCE),
          source.toString()
        ),
        Map.entry(
          strings.format(TARGET),
          target.toString()
        )
      ),
      Optional.empty()
    );
  }
}
