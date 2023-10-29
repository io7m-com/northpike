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


package com.io7m.northpike.tests.agent.workexec;

import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.agent.workexec.api.NPAWorkEvent;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorConfiguration;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorContainerImage;
import com.io7m.northpike.agent.workexec.podman.NPWorkExecutorsPodman;
import com.io7m.northpike.model.NPArchiveLinks;
import com.io7m.northpike.model.NPCleanImmediately;
import com.io7m.northpike.model.NPFailureIgnore;
import com.io7m.northpike.model.NPToolExecutionEvaluated;
import com.io7m.northpike.model.NPToolName;
import com.io7m.northpike.model.NPToolReference;
import com.io7m.northpike.model.NPToolReferenceName;
import com.io7m.northpike.model.NPWorkItemIdentifier;
import com.io7m.northpike.model.agents.NPAgentWorkItem;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionID;
import com.io7m.northpike.tools.maven.NPTMFactory3;
import com.io7m.quixote.core.QWebServerAddresses;
import com.io7m.quixote.core.QWebServerType;
import com.io7m.quixote.core.QWebServers;
import com.io7m.repetoir.core.RPServiceDirectory;
import com.io7m.verona.core.Version;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;
import java.util.concurrent.Flow;
import java.util.concurrent.LinkedBlockingQueue;

import static com.io7m.northpike.agent.workexec.api.NPAWorkExecutionResult.FAILURE;
import static com.io7m.northpike.agent.workexec.api.NPAWorkExecutionResult.SUCCESS;
import static com.io7m.northpike.tests.NPTestProperties.WORKEXEC_DISTRIBUTION;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

public final class NPWorkExecutorsPodmanTest
  implements Flow.Subscriber<NPAWorkEvent>
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPWorkExecutorsPodmanTest.class);

  private NPWorkExecutorsPodman executors;
  private RPServiceDirectory services;
  private QWebServerType server;
  private LinkedBlockingQueue<NPAWorkEvent> events;

  @BeforeEach
  public void setup()
    throws Exception
  {
    this.services =
      new RPServiceDirectory();
    this.executors =
      new NPWorkExecutorsPodman();
    this.events =
      new LinkedBlockingQueue<>();

    final var publicIp =
      QWebServerAddresses.findPublicIP();

    assumeTrue(publicIp.isPresent());

    this.server =
      QWebServers.createServerForSpecific(publicIp.orElseThrow(), 20000);
  }

  @AfterEach
  public void tearDown()
    throws Exception
  {
    this.server.close();
  }

  @Test
  public void testEnvironment(
    final @TempDir Path workDirectory,
    final @TempDir Path tmpDirectory)
    throws Exception
  {
    assumeTrue(this.executors.isSupported());

    try (var executor =
           this.executors.createExecutor(
             this.services,
             standardConfiguration(workDirectory, tmpDirectory))) {
      final var env = executor.environment();
      assertEquals("northpike", env.get("HOSTNAME"));
      env.forEach((key, val) -> LOG.debug("Environment: {} {}", key, val));
    }
  }

  @Test
  public void testProperties(
    final @TempDir Path workDirectory,
    final @TempDir Path tmpDirectory)
    throws Exception
  {
    assumeTrue(this.executors.isSupported());

    try (var executor =
           this.executors.createExecutor(
             this.services,
             standardConfiguration(workDirectory, tmpDirectory))) {
      final var env = executor.systemProperties();
      assertEquals("65.0", env.get("java.class.version"));
      env.forEach((key, val) -> LOG.debug("Property: {} {}", key, val));
    }
  }

  @Test
  public void testExecuteArchive404(
    final @TempDir Path workDirectory,
    final @TempDir Path tmpDirectory)
    throws Exception
  {
    assumeTrue(this.executors.isSupported());

    this.server.addResponse()
      .forPath("/archive.tar.gz")
      .withStatus(404);

    this.server.addResponse()
      .forPath("/archive.tar.gz.sha512")
      .withStatus(404);

    try (var executor =
           this.executors.createExecutor(
             this.services,
             standardConfiguration(workDirectory, tmpDirectory))) {

      final var workItem =
        new NPAgentWorkItem(
          new NPWorkItemIdentifier(
            new NPAssignmentExecutionID(UUID.randomUUID()),
            new RDottedName("x")
          ),
          Map.of(),
          Set.of(),
          new NPToolExecutionEvaluated(
            new NPToolReference(
              NPToolReferenceName.of("t"),
              NPToolName.of("u"),
              Version.of(1, 0, 0)
            ),
            Map.of(),
            List.of()
          ),
          new NPArchiveLinks(
            this.server.uri().resolve("archive.tar.gz"),
            this.server.uri().resolve("archive.tar.gz.sha512")
          ),
          Set.of(),
          NPFailureIgnore.IGNORE_FAILURE,
          NPCleanImmediately.CLEAN_IMMEDIATELY
        );

      try (var execution = executor.createExecution(workItem)) {
        execution.events().subscribe(this);
        final var result = execution.execute();
        assertEquals(FAILURE, result);
      }
    }

    /*
     * A 404 error was logged.
     */

    assertTrue(
      this.events.stream()
        .anyMatch(event -> {
          return Objects.equals(event.attributes().get("Status"), "404");
        })
    );
  }

  @Test
  public void testExecuteTrivial(
    final @TempDir Path workDirectory,
    final @TempDir Path tmpDirectory)
    throws Exception
  {
    assumeTrue(this.executors.isSupported());

    this.server.addResponse()
      .forPath("/archive.tar.gz")
      .withStatus(200)
      .withFixedData(resource("trivial.tar.gz"));

    this.server.addResponse()
      .forPath("/archive.tar.gz.sha512")
      .withStatus(200)
      .withFixedData(resource("trivial.tar.gz.sha512"));

    try (var executor =
           this.executors.createExecutor(
             this.services,
             standardConfiguration(workDirectory, tmpDirectory))) {

      final var toolReference =
        new NPToolReference(
          NPToolReferenceName.of("maven"),
          new NPTMFactory3().toolName(),
          new NPTMFactory3().toolVersions().lower()
        );

      final var workItem =
        new NPAgentWorkItem(
          new NPWorkItemIdentifier(
            new NPAssignmentExecutionID(UUID.randomUUID()),
            new RDottedName("x")
          ),
          Map.of(),
          Set.of(toolReference),
          new NPToolExecutionEvaluated(
            toolReference,
            Map.of(
              "JAVA_HOME", "/opt/java/openjdk"
            ),
            List.of("clean")
          ),
          new NPArchiveLinks(
            this.server.uri().resolve("archive.tar.gz"),
            this.server.uri().resolve("archive.tar.gz.sha512")
          ),
          Set.of(),
          NPFailureIgnore.IGNORE_FAILURE,
          NPCleanImmediately.CLEAN_IMMEDIATELY
        );

      try (var execution = executor.createExecution(workItem)) {
        execution.events().subscribe(this);
        final var result = execution.execute();
        assertEquals(SUCCESS, result);
      }
    }
  }

  private static NPAWorkExecutorConfiguration standardConfiguration(
    final Path workDirectory,
    final Path tmpDirectory)
  {
    return NPAWorkExecutorConfiguration.builder()
      .setWorkspaceDirectory(workDirectory)
      .setTemporaryDirectory(tmpDirectory)
      .setWorkExecDistributionDirectory(WORKEXEC_DISTRIBUTION)
      .setContainerImage(new NPAWorkExecutorContainerImage(
        "docker.io",
        "eclipse-temurin",
        "21-jre-alpine",
        Optional.empty()
      ))
      .build();
  }

  @Override
  public void onSubscribe(
    final Flow.Subscription subscription)
  {
    subscription.request(Long.MAX_VALUE);
  }

  @Override
  public void onNext(
    final NPAWorkEvent item)
  {
    LOG.debug("Event: {}", item);
    this.events.add(item);
  }

  @Override
  public void onError(
    final Throwable throwable)
  {
    LOG.debug("Error: ", throwable);
  }

  @Override
  public void onComplete()
  {

  }

  private static byte[] resource(
    final String name)
    throws IOException
  {
    final var path =
      "/com/io7m/northpike/tests/%s".formatted(name);

    return NPWorkExecutorsPodmanTest.class
      .getResourceAsStream(path)
      .readAllBytes();
  }
}
