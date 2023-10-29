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


package com.io7m.northpike.agent.workexec.api;

import com.io7m.jmulticlose.core.CloseableType;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.agents.NPAgentWorkItem;

import java.util.Map;

/**
 * A work executor.
 */

public interface NPAWorkExecutorType
  extends CloseableType
{
  /**
   * Obtain a read-only view of the environment variables that would be
   * used when executing work.
   *
   * @return The environment variables
   *
   * @throws NPException On errors
   */

  Map<String, String> environment()
    throws NPException;

  /**
   * Obtain a read-only view of the system properties.
   *
   * @return The Java system properties
   *
   * @throws NPException On errors
   */

  Map<String, String> systemProperties()
    throws NPException;

  /**
   * Create an execution for the given work item.
   *
   * @param workItem The work item
   *
   * @return The execution
   *
   * @throws NPException On errors
   */

  NPAWorkExecutionType createExecution(
    NPAgentWorkItem workItem)
    throws NPException;

  @Override
  void close()
    throws NPException;
}
