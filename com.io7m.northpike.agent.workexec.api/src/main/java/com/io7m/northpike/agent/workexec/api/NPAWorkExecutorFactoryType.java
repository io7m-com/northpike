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

import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.model.NPException;
import com.io7m.repetoir.core.RPServiceDirectoryType;

import java.util.Set;

/**
 * <p>A factory of work executors.</p>
 *
 * <p>Applications are expected to load instances of these factories using
 * {@link java.util.ServiceLoader} and pick an appropriate instance.</p>
 */

public interface NPAWorkExecutorFactoryType
{
  /**
   * @return The name of the work executor
   */

  RDottedName name();

  /**
   * A read-only view of the properties exposed by the work executor.
   *
   * @return The properties
   */

  Set<NPAWorkExecutorPropertyType> properties();

  /**
   * @return {@code true} if the executor is supported on the current system
   *
   * @throws NPException On errors
   */

  boolean isSupported()
    throws NPException;

  /**
   * Create an executor.
   *
   * @param services      The service directory
   * @param configuration The configuration
   *
   * @return An executor
   *
   * @throws NPException On errors
   */

  NPAWorkExecutorType createExecutor(
    RPServiceDirectoryType services,
    NPAWorkExecutorConfiguration configuration)
    throws NPException;
}
