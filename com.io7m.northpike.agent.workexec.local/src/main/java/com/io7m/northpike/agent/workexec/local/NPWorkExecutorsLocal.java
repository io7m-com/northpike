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


package com.io7m.northpike.agent.workexec.local;

import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorConfiguration;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorFactoryType;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorPropertyType;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorType;
import com.io7m.northpike.agent.workexec.local.internal.NPWorkLocalExecutor;
import com.io7m.repetoir.core.RPServiceDirectoryType;

import java.util.Objects;
import java.util.Set;

import static com.io7m.northpike.agent.workexec.api.NPAWorkExecutorPropertyStandard.PROPERTY_LOCAL;

/**
 * A work executor that executes work on the host system directly.
 */

public final class NPWorkExecutorsLocal
  implements NPAWorkExecutorFactoryType
{
  private static final RDottedName NAME =
    new RDottedName("workexec.local");

  /**
   * A work executor that executes work on the host system directly.
   */

  public NPWorkExecutorsLocal()
  {

  }

  @Override
  public RDottedName name()
  {
    return NAME;
  }

  @Override
  public Set<NPAWorkExecutorPropertyType> properties()
  {
    return Set.of(PROPERTY_LOCAL);
  }

  @Override
  public boolean isSupported()
  {
    return true;
  }

  @Override
  public NPAWorkExecutorType createExecutor(
    final RPServiceDirectoryType services,
    final NPAWorkExecutorConfiguration configuration)
  {
    Objects.requireNonNull(services, "services");
    Objects.requireNonNull(configuration, "configuration");

    return new NPWorkLocalExecutor(services, configuration);
  }

  @Override
  public String description()
  {
    return "Local work executor.";
  }
}
