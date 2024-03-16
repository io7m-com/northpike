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


package com.io7m.northpike.agent.workexec.podman.internal;

import com.io7m.northpike.agent.locks.NPAgentResourceLockServiceType;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutionType;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorConfiguration;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorContainerImage;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorType;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.model.agents.NPAgentWorkItem;
import com.io7m.northpike.strings.NPStringConstantType;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.tavella.api.PodmanExecutableType;
import com.io7m.tavella.api.PodmanImage;
import com.io7m.tavella.api.PodmanVolumeFlag;
import com.io7m.tavella.api.PodmanVolumeMount;
import com.io7m.tavella.api.PodmanVolumeMountSourceType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.nio.file.Path;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.TreeMap;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.atomic.AtomicBoolean;

import static com.io7m.northpike.strings.NPStringConstants.CONTAINER_IMAGE;
import static com.io7m.northpike.strings.NPStringConstants.CONTAINER_REGISTRY;
import static com.io7m.northpike.strings.NPStringConstants.CONTAINER_TAG;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_EXTERNAL_PROGRAM_FAILED;
import static com.io7m.northpike.strings.NPStringConstants.PROGRAM;
import static java.util.Map.entry;

/**
 * An executor that executes work items inside Podman containers.
 */

public final class NPWorkExecutorPodman implements NPAWorkExecutorType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPWorkExecutorPodman.class);

  private final NPStrings strings;
  private final NPAgentResourceLockServiceType locks;
  private final NPAWorkExecutorConfiguration configuration;
  private final PodmanExecutableType podman;
  private final NPAgentLocalName agentName;
  private final NPAWorkExecutorContainerImage containerImage;
  private final Path workExecPath;
  private final AtomicBoolean closed;
  private final PodmanImage podmanImage;
  private final PodmanVolumeMount workExecVolume;

  /**
   * An executor that executes work items inside Podman containers.
   *
   * @param inStrings        The string resources
   * @param inLocks          The resource lock service
   * @param inConfiguration  The configuration
   * @param inPodman         The podman executable
   * @param inAgentName      The agent name
   * @param inContainerImage The container image used for work items
   * @param inWorkExecPath   The path to the workexec distribution
   */

  public NPWorkExecutorPodman(
    final NPStrings inStrings,
    final NPAgentResourceLockServiceType inLocks,
    final NPAWorkExecutorConfiguration inConfiguration,
    final PodmanExecutableType inPodman,
    final NPAgentLocalName inAgentName,
    final NPAWorkExecutorContainerImage inContainerImage,
    final Path inWorkExecPath)
  {
    this.strings =
      Objects.requireNonNull(inStrings, "inStrings");
    this.locks =
      Objects.requireNonNull(inLocks, "locks");
    this.configuration =
      Objects.requireNonNull(inConfiguration, "configuration");
    this.podman =
      Objects.requireNonNull(inPodman, "podman");
    this.agentName =
      Objects.requireNonNull(inAgentName, "inAgentName");
    this.containerImage =
      Objects.requireNonNull(inContainerImage, "containerImage");
    this.workExecPath =
      Objects.requireNonNull(inWorkExecPath, "workExecPath");
    this.closed =
      new AtomicBoolean(false);
    this.podmanImage =
      new PodmanImage(
        this.containerImage.registry(),
        this.containerImage.name(),
        this.containerImage.tag(),
        this.containerImage.hash()
      );

    this.workExecVolume =
      new PodmanVolumeMount(
        new PodmanVolumeMountSourceType.HostPath(this.workExecPath),
        "/northpike-workexec",
        Set.of(
          PodmanVolumeFlag.READ_ONLY,
          PodmanVolumeFlag.NO_DEVICES,
          PodmanVolumeFlag.NO_SETUID,
          PodmanVolumeFlag.SELINUX_LABEL_SHARED
        )
      );
  }

  @Override
  public Map<String, String> environment()
    throws NPException
  {
    final var outputLines =
      this.runWorkExecCommand("environment");

    final var output = new TreeMap<String, String>();
    for (final var line : outputLines) {
      final var segments = line.split("=");
      output.put(segments[0], segments[1]);
    }

    return output;
  }

  private LinkedBlockingQueue<String> runWorkExecCommand(
    final String command)
    throws NPException
  {
    try {
      final var process =
        this.podman.run()
          .setInteractive(true)
          .setImage(this.podmanImage)
          .setRemoveAfterExit(true)
          .addEnvironmentVariable(
            "NORTHPIKE_WORKEXEC_HOME",
            "/northpike-workexec")
          .addEnvironmentVariable("HOSTNAME", "northpike")
          .addVolume(this.workExecVolume)
          .addArgument("/northpike-workexec/bin/northpike-workexec")
          .addArgument(command)
          .build()
          .start();

      final var outputLines =
        new LinkedBlockingQueue<String>();

      final var outThread =
        Thread.ofVirtual()
          .start(() -> {
            try (var reader = process.inputReader()) {
              outputLines.addAll(reader.lines().toList());
            } catch (final IOException e) {
              LOG.error(
                "Failed to read process {} output: ",
                Long.valueOf(process.pid()),
                e
              );
            }
          });

      final var errThread =
        Thread.ofVirtual()
          .start(() -> {
            try (var reader = process.errorReader()) {
              for (final var line : reader.lines().toList()) {
                LOG.info("[{}] {}", Long.valueOf(process.pid()), line);
              }
            } catch (final IOException e) {
              LOG.error(
                "Failed to read process {} error output: ",
                Long.valueOf(process.pid()),
                e
              );
            }
          });

      process.waitFor();
      outThread.join();
      errThread.join();

      if (process.exitValue() != 0) {
        throw new IOException(this.localize(ERROR_EXTERNAL_PROGRAM_FAILED));
      }

      return outputLines;
    } catch (final Exception e) {
      throw new NPException(
        e.getMessage(),
        e,
        NPStandardErrorCodes.errorIo(),
        Map.ofEntries(
          entry(
            this.localize(PROGRAM),
            "/northpike-workexec/bin/northpike-workexec"),
          entry(
            this.localize(CONTAINER_IMAGE), this.containerImage.name()),
          entry(
            this.localize(CONTAINER_TAG), this.containerImage.tag()),
          entry(
            this.localize(CONTAINER_REGISTRY), this.containerImage.registry())
        ),
        Optional.empty()
      );
    }
  }

  private String localize(
    final NPStringConstantType c)
  {
    return this.strings.format(c);
  }

  @Override
  public Map<String, String> systemProperties()
    throws NPException
  {
    final var outputLines =
      this.runWorkExecCommand("properties");

    final var output = new TreeMap<String, String>();
    for (final var line : outputLines) {
      final var segments = line.split("=");
      if (segments.length == 2) {
        output.put(segments[0], segments[1]);
      }
    }

    return output;
  }

  @Override
  public NPAWorkExecutionType createExecution(
    final NPAgentWorkItem workItem)
  {
    return new NPWorkExecutionPodman(
      this.strings,
      this.locks,
      this.configuration,
      this.agentName,
      this.podman,
      this.podmanImage,
      this.workExecVolume,
      workItem
    );
  }

  @Override
  public void close()
    throws NPException
  {
    if (this.closed.compareAndSet(false, true)) {
      // Nothing at the moment
    }
  }

  @Override
  public boolean isClosed()
  {
    return this.closed.get();
  }
}
