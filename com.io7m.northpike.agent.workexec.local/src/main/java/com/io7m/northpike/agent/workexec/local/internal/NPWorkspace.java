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


package com.io7m.northpike.agent.workexec.local.internal;

import com.io7m.northpike.model.NPCleanImmediately;
import com.io7m.northpike.model.NPCleanLater;
import com.io7m.northpike.model.agents.NPAgentWorkItem;
import org.apache.commons.io.file.PathUtils;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.Closeable;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Objects;

import static org.apache.commons.io.file.StandardDeleteOption.OVERRIDE_READ_ONLY;

/**
 * A workspace for a work item.
 */

public final class NPWorkspace implements Closeable
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPWorkspace.class);

  private final NPAgentWorkItem workItem;
  private final Path assignmentDirectory;
  private final Path toolsDirectory;
  private final Path sourceDirectory;
  private final Path archiveDirectory;

  private NPWorkspace(
    final NPAgentWorkItem inWorkItem,
    final Path inAssignmentDirectory,
    final Path inToolsDirectory,
    final Path inSourceDirectory,
    final Path inArchiveDirectory)
  {
    this.workItem =
      Objects.requireNonNull(inWorkItem, "workItem");
    this.assignmentDirectory =
      Objects.requireNonNull(inAssignmentDirectory, "assignmentDirectory");
    this.toolsDirectory =
      Objects.requireNonNull(inToolsDirectory, "toolsDirectory");
    this.sourceDirectory =
      Objects.requireNonNull(inSourceDirectory, "sourceDirectory");
    this.archiveDirectory =
      Objects.requireNonNull(inArchiveDirectory, "archiveDirectory");
  }

  /**
   * Open a fresh workspace.
   *
   * @param baseDirectory The base directory
   * @param workItem      The work item
   *
   * @return A fresh workspace
   *
   * @throws IOException On I/O errors
   */

  public static NPWorkspace open(
    final Path baseDirectory,
    final NPAgentWorkItem workItem)
    throws IOException
  {
    final var workspaceDirectory =
      baseDirectory.resolve("workspaces");

    final var assignmentDirectory =
      workspaceDirectory.resolve(
        workItem.identifier()
          .assignmentExecutionId()
          .toString()
      );

    final var toolsDirectory =
      assignmentDirectory.resolve("tools");
    final var sourceDirectory =
      assignmentDirectory.resolve("source");
    final var archiveDirectory =
      assignmentDirectory.resolve("archives");

    Files.createDirectories(toolsDirectory);
    Files.createDirectories(sourceDirectory);
    Files.createDirectories(archiveDirectory);

    return new NPWorkspace(
      workItem,
      assignmentDirectory,
      toolsDirectory,
      sourceDirectory,
      archiveDirectory
    );
  }

  /**
   * @return The work item
   */

  public NPAgentWorkItem workItem()
  {
    return this.workItem;
  }

  /**
   * @return The base assignment directory
   */

  public Path assignmentDirectory()
  {
    return this.assignmentDirectory;
  }

  /**
   * @return The tools directory inside the assignment directory
   */

  public Path toolsDirectory()
  {
    return this.toolsDirectory;
  }

  /**
   * @return The source directory inside the assignment directory
   */

  public Path sourceDirectory()
  {
    return this.sourceDirectory;
  }

  /**
   * @return The archive directory inside the assignment directory
   */

  public Path archiveDirectory()
  {
    return this.archiveDirectory;
  }

  @Override
  public void close()
    throws IOException
  {
    switch (this.workItem.cleanPolicy()) {
      case final NPCleanImmediately immediately -> {
        LOG.info("Deleting workspace {}", this.assignmentDirectory);
        PathUtils.deleteDirectory(
          this.assignmentDirectory,
          OVERRIDE_READ_ONLY
        );
      }
      case final NPCleanLater later -> {

      }
    }
  }
}
