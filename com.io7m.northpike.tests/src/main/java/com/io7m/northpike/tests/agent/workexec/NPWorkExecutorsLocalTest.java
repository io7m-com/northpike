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
import com.io7m.northpike.agent.locks.NPAgentResourceLockService;
import com.io7m.northpike.agent.locks.NPAgentResourceLockServiceType;
import com.io7m.northpike.agent.workexec.api.NPAWorkEvent;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecName;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorConfiguration;
import com.io7m.northpike.agent.workexec.local.NPWorkExecutorsLocal;
import com.io7m.northpike.model.NPArchiveLinks;
import com.io7m.northpike.model.NPCleanImmediately;
import com.io7m.northpike.model.NPFailureFail;
import com.io7m.northpike.model.NPToolExecutionEvaluated;
import com.io7m.northpike.model.NPToolName;
import com.io7m.northpike.model.NPToolReference;
import com.io7m.northpike.model.NPToolReferenceName;
import com.io7m.northpike.model.NPWorkItemIdentifier;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.model.agents.NPAgentWorkItem;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionID;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.tools.api.NPToolFactoryType;
import com.io7m.northpike.tools.maven.NPTMFactory3;
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
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.UUID;
import java.util.concurrent.Flow;

import static com.io7m.northpike.agent.workexec.api.NPAWorkExecutionResult.SUCCESS;
import static com.io7m.northpike.tests.containers.NPFixtures.webServerPort;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

public final class NPWorkExecutorsLocalTest
  implements Flow.Subscriber<NPAWorkEvent>
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPWorkExecutorsLocalTest.class);

  private NPWorkExecutorsLocal executors;
  private RPServiceDirectory services;
  private NPStrings strings;
  private QWebServerType server;

  @BeforeEach
  public void setup()
    throws IOException
  {
    this.strings = NPStrings.create(Locale.ROOT);
    this.services = new RPServiceDirectory();
    this.services.register(
      NPStrings.class,
      this.strings
    );
    this.services.register(
      NPToolFactoryType.class,
      new NPTMFactory3()
    );
    this.services.register(
      NPAgentResourceLockServiceType.class,
      NPAgentResourceLockService.create()
    );

    this.executors = new NPWorkExecutorsLocal();
    this.server = QWebServers.createServer(webServerPort() + 1);
  }

  @AfterEach
  public void tearDown()
    throws IOException
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

    try (var executor = this.executors.createExecutor(
      this.services,
      NPAgentLocalName.of("agent"),
      NPAWorkExecutorConfiguration.builder()
        .setWorkDirectory(workDirectory)
        .setTemporaryDirectory(tmpDirectory)
        .setExecutorType(NPAWorkExecName.of("workexec.local"))
        .build()
    )) {
      final var env = executor.environment();
      env.forEach((key, val) -> LOG.debug("Environment: {} {}", key, val));
    }
  }

  @Test
  public void testExecuteWorkItem(
    final @TempDir Path workDirectory,
    final @TempDir Path tmpDirectory)
    throws Exception
  {
    assumeTrue(this.executors.isSupported());

    final var mavenReference =
      new NPToolReference(
        NPToolReferenceName.of("maven"),
        NPToolName.of("org.apache.maven"),
        Version.of(3, 9, 1)
      );

    this.server.addResponse()
      .forPath("/file.tar.gz")
      .withStatus(200)
      .withFixedData(resource("trivial.tar.gz"));

    this.server.addResponse()
      .forPath("/file.tar.gz.sha512")
      .withStatus(200)
      .withFixedData(resource("trivial.tar.gz.sha512"));

    final var workItem =
      new NPAgentWorkItem(
        new NPWorkItemIdentifier(
          new NPAssignmentExecutionID(UUID.randomUUID()),
          new RDottedName("build")
        ),
        Map.of(),
        Set.of(mavenReference),
        new NPToolExecutionEvaluated(
          mavenReference,
          System.getenv(),
          List.of("clean")
        ),
        new NPArchiveLinks(
          this.server.uri().resolve("file.tar.gz"),
          this.server.uri().resolve("file.tar.gz.sha512")
        ),
        Set.of(),
        NPFailureFail.FAIL,
        NPCleanImmediately.CLEAN_IMMEDIATELY
      );

    try (var executor = this.executors.createExecutor(
      this.services,
      NPAgentLocalName.of("agent"),
      NPAWorkExecutorConfiguration.builder()
        .setWorkDirectory(workDirectory)
        .setTemporaryDirectory(tmpDirectory)
        .setExecutorType(NPAWorkExecName.of("workexec.local"))
        .build()
    )) {
      try (var execution = executor.createExecution(workItem)) {
        execution.events().subscribe(this);
        final var result = execution.execute();
        assertEquals(SUCCESS, result);
      }
    }
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
    LOG.debug("{}", item);
  }

  @Override
  public void onError(
    final Throwable throwable)
  {

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

    return NPWorkExecutorsLocalTest.class
      .getResourceAsStream(path)
      .readAllBytes();
  }
}
