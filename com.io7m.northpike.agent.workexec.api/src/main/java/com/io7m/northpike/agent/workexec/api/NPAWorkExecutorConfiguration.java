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

import java.nio.file.Path;
import java.util.Objects;
import java.util.Optional;

/**
 * The configuration for an executor.
 */

public final class NPAWorkExecutorConfiguration
{
  private final NPAWorkExecName type;
  private final Optional<NPAWorkExecutorContainerImage> containerImage;
  private final Optional<String> podName;
  private final Path workDirectory;
  private final Optional<Path> workExecDistributionDirectory;
  private final Path temporaryDirectory;

  private NPAWorkExecutorConfiguration(
    final NPAWorkExecName inType,
    final Optional<NPAWorkExecutorContainerImage> inContainerImage,
    final Optional<String> inPodName,
    final Path inWorkspaceDirectory,
    final Path inTmpDirectory,
    final Optional<Path> inWorkExecDistributionDirectory)
  {
    this.type =
      Objects.requireNonNull(inType, "type");
    this.containerImage =
      Objects.requireNonNull(inContainerImage, "containerImage");
    this.podName =
      Objects.requireNonNull(inPodName, "podName");
    this.workDirectory =
      Objects.requireNonNull(inWorkspaceDirectory, "workDirectory");
    this.temporaryDirectory =
      Objects.requireNonNull(inTmpDirectory, "temporaryDirectory");
    this.workExecDistributionDirectory =
      Objects.requireNonNull(
        inWorkExecDistributionDirectory,
        "workExecDistributionDirectory"
      );
  }

  /**
   * @return The executor type
   */

  public NPAWorkExecName type()
  {
    return this.type;
  }

  /**
   * @return A new mutable configuration builder
   */

  public static Builder builder()
  {
    return new Builder();
  }

  /**
   * @return The directory used to hold temporary data
   */

  public Path temporaryDirectory()
  {
    return this.temporaryDirectory;
  }

  /**
   * @return The container image used for builds
   */

  public Optional<NPAWorkExecutorContainerImage> containerImage()
  {
    return this.containerImage;
  }

  /**
   * @return The container pod name
   */

  public Optional<String> containerPodName()
  {
    return this.podName;
  }

  /**
   * @return The base directory that will contain workspace directories and
   * potentially non-volatile data
   */

  public Path workDirectory()
  {
    return this.workDirectory;
  }

  /**
   * @return A read-only directory mounted into containers that contains the
   * workexec distribution
   */

  public Optional<Path> workExecDistributionDirectory()
  {
    return this.workExecDistributionDirectory;
  }

  @Override
  public boolean equals(final Object o)
  {
    if (this == o) {
      return true;
    }
    if (o == null || !this.getClass().equals(o.getClass())) {
      return false;
    }
    final NPAWorkExecutorConfiguration that = (NPAWorkExecutorConfiguration) o;
    return Objects.equals(this.type, that.type)
           && Objects.equals(this.containerImage, that.containerImage)
           && Objects.equals(this.workDirectory, that.workDirectory)
           && Objects.equals(
      this.workExecDistributionDirectory,
      that.workExecDistributionDirectory)
           && Objects.equals(this.temporaryDirectory, that.temporaryDirectory);
  }

  @Override
  public int hashCode()
  {
    return Objects.hash(
      this.type,
      this.containerImage,
      this.workDirectory,
      this.workExecDistributionDirectory,
      this.temporaryDirectory
    );
  }

  /**
   * A mutable builder for configurations.
   */

  public static final class Builder
  {
    private NPAWorkExecName type;
    private Optional<Path> workExecDistributionDirectory;
    private Optional<NPAWorkExecutorContainerImage> containerImage;
    private Path workDirectory;
    private Path temporaryDirectory;
    private Optional<String> podName;

    Builder()
    {
      this.containerImage =
        Optional.empty();
      this.workExecDistributionDirectory =
        Optional.empty();
      this.podName =
        Optional.empty();
    }

    /**
     * Set the executor type used for builds.
     *
     * @param t The executor type
     *
     * @return this
     */

    public Builder setExecutorType(
      final NPAWorkExecName t)
    {
      this.type = Objects.requireNonNull(t, "t");
      return this;
    }

    /**
     * Set the container image used for builds.
     *
     * @param i The image
     *
     * @return this
     */

    public Builder setContainerImage(
      final NPAWorkExecutorContainerImage i)
    {
      this.containerImage = Optional.of(i);
      return this;
    }

    /**
     * @return An immutable configuration based on the values given so far
     */

    public NPAWorkExecutorConfiguration build()
    {
      return new NPAWorkExecutorConfiguration(
        this.type,
        this.containerImage,
        this.podName,
        this.workDirectory,
        this.temporaryDirectory,
        this.workExecDistributionDirectory
      );
    }

    /**
     * Set the directory that will contain works.
     *
     * @param directory The base directory
     *
     * @return this
     */

    public Builder setWorkDirectory(
      final Path directory)
    {
      this.workDirectory =
        Objects.requireNonNull(directory, "directory");
      return this;
    }

    /**
     * Set the directory that will contain temporary data.
     *
     * @param directory The base directory
     *
     * @return this
     */

    public Builder setTemporaryDirectory(
      final Path directory)
    {
      this.temporaryDirectory =
        Objects.requireNonNull(directory, "directory");
      return this;
    }

    /**
     * Set the directory that contains the workexec distribution.
     *
     * @param directory The directory
     *
     * @return this
     */

    public Builder setWorkExecDistributionDirectory(
      final Path directory)
    {
      this.workExecDistributionDirectory = Optional.of(directory);
      return this;
    }

    /**
     * Set the podman pod within which containers will be created.
     * @param name The pod name
     * @return this
     */

    public Builder setContainerPod(
      final String name)
    {
      this.podName = Optional.of(name);
      return this;
    }
  }
}
