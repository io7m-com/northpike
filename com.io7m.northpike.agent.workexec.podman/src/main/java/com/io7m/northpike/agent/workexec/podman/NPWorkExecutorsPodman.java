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


package com.io7m.northpike.agent.workexec.podman;

import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorConfiguration;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorFactoryType;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorPropertyType;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorType;
import com.io7m.northpike.agent.workexec.podman.internal.NPWorkExecutorPodman;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.repetoir.core.RPServiceDirectoryType;
import com.io7m.tavella.api.PodmanExecutableConfiguration;
import com.io7m.tavella.api.PodmanExecutableFactoryType;
import com.io7m.tavella.api.PodmanExecutableType;
import com.io7m.tavella.native_exec.PodmanNative;

import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

import static com.io7m.northpike.agent.workexec.api.NPAWorkExecutorPropertyStandard.PROPERTY_CONTAINERIZED;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorIo;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_NO_CONTAINER_IMAGE;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_NO_CONTAINER_IMAGE_REMEDIATE;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_NO_WORKEXEC;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_NO_WORKEXEC_REMEDIATE;

/**
 * An executor that executes work items inside Podman containers.
 */

public final class NPWorkExecutorsPodman
  implements NPAWorkExecutorFactoryType
{
  private static final RDottedName NAME =
    new RDottedName("workexec.podman");

  private final PodmanExecutableFactoryType executables;
  private final NPStrings strings;

  /**
   * An executor that executes work items inside Podman containers.
   */

  public NPWorkExecutorsPodman()
  {
    this(new PodmanNative(), Locale.getDefault());
  }

  /**
   * An executor that executes work items inside Podman containers.
   *
   * @param inExecutables A provider of podman executables
   */

  public NPWorkExecutorsPodman(
    final PodmanExecutableFactoryType inExecutables)
  {
    this(inExecutables, Locale.getDefault());
  }

  /**
   * An executor that executes work items inside Podman containers.
   *
   * @param inExecutables A provider of podman executables
   * @param locale        The locale for string resources
   */

  public NPWorkExecutorsPodman(
    final PodmanExecutableFactoryType inExecutables,
    final Locale locale)
  {
    this(inExecutables, NPStrings.create(locale));
  }

  /**
   * An executor that executes work items inside Podman containers.
   *
   * @param inExecutables A provider of podman executables
   * @param inStrings     The string resources
   */

  public NPWorkExecutorsPodman(
    final PodmanExecutableFactoryType inExecutables,
    final NPStrings inStrings)
  {
    this.executables =
      Objects.requireNonNull(inExecutables, "supervisors");
    this.strings =
      Objects.requireNonNull(inStrings, "strings");
  }

  @Override
  public RDottedName name()
  {
    return NAME;
  }

  @Override
  public Set<NPAWorkExecutorPropertyType> properties()
  {
    return Set.of(PROPERTY_CONTAINERIZED);
  }

  @Override
  public boolean isSupported()
  {
    try {
      return this.executables.isSupported(
        PodmanExecutableConfiguration.builder()
          .build()
      ).isPresent();
    } catch (final InterruptedException e) {
      return false;
    }
  }

  @Override
  public NPAWorkExecutorType createExecutor(
    final RPServiceDirectoryType services,
    final NPAWorkExecutorConfiguration configuration)
    throws NPException
  {
    Objects.requireNonNull(services, "services");
    Objects.requireNonNull(configuration, "configuration");

    final var imageOpt = configuration.containerImage();
    if (imageOpt.isEmpty()) {
      throw this.errorNoContainerImage();
    }

    final var workExecOpt = configuration.workExecDistributionDirectory();
    if (workExecOpt.isEmpty()) {
      throw this.errorNoWorkExec();
    }

    final PodmanExecutableType executable;
    try {
      executable = this.executables.createExecutable(
        PodmanExecutableConfiguration.builder()
          .build()
      );
    } catch (final Exception e) {
      throw new NPException(
        e.getMessage(),
        e,
        errorIo(),
        Map.of(),
        Optional.empty()
      );
    }

    return new NPWorkExecutorPodman(
      this.strings,
      configuration,
      executable,
      imageOpt.get(),
      workExecOpt.get()
    );
  }

  private NPException errorNoWorkExec()
  {
    return new NPException(
      this.strings.format(ERROR_NO_WORKEXEC),
      NPStandardErrorCodes.errorConfiguration(),
      Map.of(),
      Optional.of(this.strings.format(ERROR_NO_WORKEXEC_REMEDIATE))
    );
  }

  private NPException errorNoContainerImage()
  {
    return new NPException(
      this.strings.format(ERROR_NO_CONTAINER_IMAGE),
      NPStandardErrorCodes.errorConfiguration(),
      Map.of(),
      Optional.of(this.strings.format(ERROR_NO_CONTAINER_IMAGE_REMEDIATE))
    );
  }
}
