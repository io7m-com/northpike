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


package com.io7m.northpike.tools.api;

import com.io7m.northpike.model.NPToolExecutionName;

import java.nio.file.Path;
import java.util.List;
import java.util.Map;
import java.util.concurrent.Flow;

/**
 * A tool instance.
 */

public interface NPToolType extends AutoCloseable
{
  /**
   * @return The factory that produced the tool
   */

  NPToolFactoryType factory();

  /**
   * @return A stream of events published by the tool
   */

  Flow.Publisher<NPToolEventType> events();

  /**
   * Install the tool. The operation is idempotent; if the tool is already
   * installed, the method returns immediately without performing another
   * install.
   *
   * @throws NPToolException      On errors
   * @throws InterruptedException On interruption
   */

  void install()
    throws NPToolException, InterruptedException;

  /**
   * Execute the given command.
   *
   * @param executionDirectory The initial execution directory
   * @param environment        The environment variables
   * @param arguments          The arguments
   *
   * @return The result of executing the command
   *
   * @throws InterruptedException On interruption
   * @throws NPToolException      On errors
   */

  NPToolProgramResult execute(
    Path executionDirectory,
    Map<String, String> environment,
    List<String> arguments)
    throws NPToolException, InterruptedException;

  /**
   * Set the download host used for install operations.
   *
   * @param host The host
   */

  void setDownloadHost(String host);

  /**
   * @return The download host that will be used for install operations
   */

  String downloadHost();

  @Override
  void close()
    throws NPToolException;

  /**
   * @return {@code true} if the tool is installed in the given directory
   */

  boolean isInstalled();

  /**
   * Enable/disable HTTPs.
   *
   * @param b {@code true} if TLS should be enabled
   */

  void setHTTPs(boolean b);

  /**
   * @return The default executions provided by the tool
   */

  default Map<NPToolExecutionName, List<String>> defaultExecutions()
  {
    return this.factory().defaultExecutions();
  }
}
