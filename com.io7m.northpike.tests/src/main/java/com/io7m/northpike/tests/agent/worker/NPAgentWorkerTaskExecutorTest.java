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


package com.io7m.northpike.tests.agent.worker;

import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.agent.internal.worker.NPAgentWorkerTaskExecutor;
import com.io7m.northpike.agent.internal.worker.NPAgentWorkerType;
import com.io7m.northpike.agent.workexec.api.NPAWorkEvent;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutionType;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorType;
import com.io7m.northpike.model.NPArchiveLinks;
import com.io7m.northpike.model.NPToolExecutionEvaluated;
import com.io7m.northpike.model.NPToolName;
import com.io7m.northpike.model.NPToolReference;
import com.io7m.northpike.model.NPToolReferenceName;
import com.io7m.northpike.model.NPWorkItemIdentifier;
import com.io7m.northpike.model.agents.NPAgentWorkItem;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionID;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.verona.core.Version;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.Mockito;
import org.mockito.internal.verification.AtLeast;
import org.mockito.internal.verification.Times;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.net.URI;
import java.time.OffsetDateTime;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;
import java.util.concurrent.SubmissionPublisher;
import java.util.concurrent.TimeUnit;

import static com.io7m.northpike.agent.workexec.api.NPAWorkExecutionResult.FAILURE;
import static com.io7m.northpike.agent.workexec.api.NPAWorkExecutionResult.SUCCESS;
import static com.io7m.northpike.model.NPCleanImmediately.CLEAN_IMMEDIATELY;
import static com.io7m.northpike.model.NPFailureFail.FAIL;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.eq;

public final class NPAgentWorkerTaskExecutorTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgentWorkerTaskExecutorTest.class);

  private NPAgentWorkerType worker;
  private NPStrings strings;
  private NPAWorkExecutorType workExec;
  private NPAgentWorkerTaskExecutor task;
  private NPWorkItemIdentifier workItem0Id;
  private NPAgentWorkItem workItem0;
  private NPAWorkExecutionType workExecution;
  private SubmissionPublisher<NPAWorkEvent> events;
  private NPAWorkEvent event0;
  private NPAWorkEvent event1;
  private NPAWorkEvent event2;

  @BeforeEach
  public void setup()
    throws Exception
  {
    this.worker =
      Mockito.mock(NPAgentWorkerType.class);
    this.strings =
      NPStrings.create(Locale.ROOT);
    this.workExec =
      Mockito.mock(NPAWorkExecutorType.class);
    this.workExecution =
      Mockito.mock(NPAWorkExecutionType.class);
    this.events =
      new SubmissionPublisher<>();

    Mockito.when(this.workExec.createExecution(any()))
      .thenReturn(this.workExecution);
    Mockito.when(this.workExecution.events())
      .thenReturn(this.events);

    this.task =
      NPAgentWorkerTaskExecutor.open(
        this.worker,
        this.workExec
      );

    this.workItem0Id =
      new NPWorkItemIdentifier(
        new NPAssignmentExecutionID(UUID.randomUUID()),
        new RDottedName("some.task")
      );

    this.workItem0 =
      new NPAgentWorkItem(
        this.workItem0Id,
        Map.of(),
        Set.of(),
        new NPToolExecutionEvaluated(
          new NPToolReference(
            NPToolReferenceName.of("x"),
            NPToolName.of("maven"),
            Version.of(1, 0, 0)
          ),
          Map.of(),
          List.of()
        ),
        new NPArchiveLinks(
          URI.create("http://www.example.com/file.tar.gz"),
          URI.create("http://www.example.com/file.tar.gz.sha256")
        ),
        Set.of(),
        FAIL,
        CLEAN_IMMEDIATELY
      );

    this.event0 =
      new NPAWorkEvent(
        NPAWorkEvent.Severity.INFO,
        OffsetDateTime.now(),
        "Event 0",
        Map.of(),
        Optional.empty()
      );
    this.event1 =
      new NPAWorkEvent(
        NPAWorkEvent.Severity.INFO,
        OffsetDateTime.now(),
        "Event 1",
        Map.of(),
        Optional.empty()
      );
    this.event2 =
      new NPAWorkEvent(
        NPAWorkEvent.Severity.INFO,
        OffsetDateTime.now(),
        "Event 2",
        Map.of(),
        Optional.empty()
      );
  }

  @AfterEach
  public void tearDown()
    throws Exception
  {
    this.task.close();
  }

  /**
   * The task relays the correct calls to the worker.
   *
   * @throws Exception On errors
   */

  @Test
  public void testBasicExecutionSucceeds()
    throws Exception
  {
    Mockito.doAnswer(invocation -> {
        this.events.submit(this.event0);
        this.events.submit(this.event1);
        this.events.submit(this.event2);
        this.events.close();
        return SUCCESS;
      })
      .when(this.workExecution)
      .execute();

    assertTrue(this.task.workCanBeAccepted(this.workItem0Id));
    assertTrue(this.task.workAccept(this.workItem0));

    this.events.consume(event -> {
      })
      .get(1L, TimeUnit.SECONDS);

    Mockito.verify(this.worker, new Times(1))
      .workStarted(this.workItem0);
    Mockito.verify(this.worker, new AtLeast(1))
      .workUpdated(eq(this.workItem0), any());
    Mockito.verify(this.worker, new Times(1))
      .workUpdated(this.workItem0, this.event0);
    Mockito.verify(this.worker, new Times(1))
      .workUpdated(this.workItem0, this.event1);
    Mockito.verify(this.worker, new Times(1))
      .workUpdated(this.workItem0, this.event2);
    Mockito.verify(this.worker, new Times(1))
      .workCompleted(this.workItem0, SUCCESS);
    Mockito.verifyNoMoreInteractions(this.worker);
  }

  /**
   * The task relays the correct calls to the worker.
   *
   * @throws Exception On errors
   */

  @Test
  public void testBasicExecutionFails()
    throws Exception
  {
    Mockito.doAnswer(invocation -> {
        this.events.submit(this.event0);
        this.events.submit(this.event1);
        this.events.submit(this.event2);
        this.events.close();
        return FAILURE;
      })
      .when(this.workExecution)
      .execute();

    assertTrue(this.task.workCanBeAccepted(this.workItem0Id));
    assertTrue(this.task.workAccept(this.workItem0));

    this.events.consume(event -> {
      })
      .get(1L, TimeUnit.SECONDS);

    Mockito.verify(this.worker, new Times(1))
      .workStarted(this.workItem0);
    Mockito.verify(this.worker, new AtLeast(1))
      .workUpdated(eq(this.workItem0), any());
    Mockito.verify(this.worker, new Times(1))
      .workUpdated(this.workItem0, this.event0);
    Mockito.verify(this.worker, new Times(1))
      .workUpdated(this.workItem0, this.event1);
    Mockito.verify(this.worker, new Times(1))
      .workUpdated(this.workItem0, this.event2);
    Mockito.verify(this.worker, new Times(1))
      .workCompleted(this.workItem0, FAILURE);
    Mockito.verifyNoMoreInteractions(this.worker);
  }

  /**
   * The task relays the correct calls to the worker.
   *
   * @throws Exception On errors
   */

  @Test
  public void testBasicExecutionCrashes()
    throws Exception
  {
    Mockito.doAnswer(invocation -> {
        this.events.close();
        return FAILURE;
      })
      .doThrow(new UnsupportedOperationException())
      .when(this.workExecution)
      .execute();

    assertTrue(this.task.workCanBeAccepted(this.workItem0Id));
    assertTrue(this.task.workAccept(this.workItem0));

    this.events.consume(event -> {
      })
      .get(1L, TimeUnit.SECONDS);

    Mockito.verify(this.worker, new Times(1))
      .workStarted(this.workItem0);
    Mockito.verify(this.worker, new Times(1))
      .workUpdated(any(), any());
    Mockito.verify(this.worker, new Times(1))
      .workCompleted(this.workItem0, FAILURE);

    Mockito.verifyNoMoreInteractions(this.worker);
  }

  /**
   * The task relays the correct calls to the worker.
   *
   * @throws Exception On errors
   */

  @Test
  public void testBasicExecutionCreationCrashes()
    throws Exception
  {
    Mockito.doThrow(new UnsupportedOperationException())
      .when(this.workExec)
      .createExecution(this.workItem0);

    assertTrue(this.task.workCanBeAccepted(this.workItem0Id));
    assertTrue(this.task.workAccept(this.workItem0));

    Mockito.verify(this.worker, new Times(1))
      .workCompleted(this.workItem0, FAILURE);

    Mockito.verifyNoMoreInteractions(this.worker);
  }
}
