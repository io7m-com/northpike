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

package com.io7m.northpike.tests.database;

import com.io7m.ervilla.api.EContainerSupervisorType;
import com.io7m.ervilla.test_extension.ErvillaCloseAfterSuite;
import com.io7m.ervilla.test_extension.ErvillaConfiguration;
import com.io7m.ervilla.test_extension.ErvillaExtension;
import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.database.api.NPDatabaseConnectionType;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.model.NPAgentDescription;
import com.io7m.northpike.model.NPAgentID;
import com.io7m.northpike.model.NPAgentLabel;
import com.io7m.northpike.model.NPAgentLabelMatchType.And;
import com.io7m.northpike.model.NPAgentLabelMatchType.Or;
import com.io7m.northpike.model.NPAgentLabelMatchType.Specific;
import com.io7m.northpike.model.NPAgentLabelSearchParameters;
import com.io7m.northpike.model.NPAgentListParameters;
import com.io7m.northpike.model.NPKey;
import com.io7m.northpike.tests.containers.NPTestContainerInstances;
import com.io7m.northpike.tests.containers.NPTestContainers;
import com.io7m.zelador.test_extension.CloseableResourcesType;
import com.io7m.zelador.test_extension.ZeladorExtension;
import net.jqwik.api.Arbitraries;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.security.NoSuchAlgorithmException;
import java.security.SecureRandom;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.UUID;
import java.util.stream.Collectors;

import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE;
import static com.io7m.northpike.model.NPAgentLabelMatchType.AnyLabel.ANY_LABEL;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

@ExtendWith({ErvillaExtension.class, ZeladorExtension.class})
@ErvillaConfiguration(projectName = "com.io7m.northpike", disabledIfUnsupported = true)
public final class NPDatabaseAgentsTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPDatabaseAgentsTest.class);

  private static NPTestContainers.NPDatabaseFixture DATABASE_FIXTURE;
  private NPDatabaseConnectionType connection;
  private NPDatabaseTransactionType transaction;
  private NPDatabaseType database;

  @BeforeAll
  public static void setupOnce(
    final @ErvillaCloseAfterSuite EContainerSupervisorType containers)
    throws Exception
  {
    DATABASE_FIXTURE = NPTestContainerInstances.database(containers);
  }

  @BeforeEach
  public void setup(
    final CloseableResourcesType closeables)
    throws Exception
  {
    DATABASE_FIXTURE.reset();

    this.database =
      closeables.addPerTestResource(DATABASE_FIXTURE.createDatabase());
    this.connection =
      closeables.addPerTestResource(this.database.openConnection(NORTHPIKE));
    this.transaction =
      closeables.addPerTestResource(this.connection.openTransaction());
  }

  /**
   * Creating agents works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAgentCreate0()
    throws Exception
  {
    final var get =
      this.transaction.queries(NPDatabaseQueriesAgentsType.GetType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesAgentsType.PutType.class);
    final var labelPut =
      this.transaction.queries(NPDatabaseQueriesAgentsType.LabelPutType.class);
    final var labelGet =
      this.transaction.queries(NPDatabaseQueriesAgentsType.LabelGetType.class);

    final var labels =
      Arbitraries.defaultFor(NPAgentLabel.class)
        .list()
        .ofMinSize(1)
        .sample();

    final var labelsByName = new HashMap<RDottedName, NPAgentLabel>();
    for (final var label : labels) {
      labelPut.execute(label);
      assertEquals(label, labelGet.execute(label.name()).orElseThrow());
      labelsByName.put(label.name(), label);
    }

    final var agent =
      new NPAgentDescription(
        new NPAgentID(UUID.randomUUID()),
        "Agent 0",
        NPKey.generate(SecureRandom.getInstanceStrong()),
        Arbitraries.maps(
          Arbitraries.strings().alpha(),
          Arbitraries.strings().alpha()
        ).sample(),
        Arbitraries.maps(
          Arbitraries.strings().alpha(),
          Arbitraries.strings().alpha()
        ).sample(),
        labelsByName
      );

    put.execute(agent);
    assertEquals(agent, get.execute(agent.id()).orElseThrow());
  }

  /**
   * Creating agents works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAgentCreate1()
    throws Exception
  {
    final var get =
      this.transaction.queries(NPDatabaseQueriesAgentsType.GetType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesAgentsType.PutType.class);
    final var labelPut =
      this.transaction.queries(NPDatabaseQueriesAgentsType.LabelPutType.class);
    final var labelGet =
      this.transaction.queries(NPDatabaseQueriesAgentsType.LabelGetType.class);

    final var labels =
      Arbitraries.defaultFor(NPAgentLabel.class)
        .list()
        .sample();

    final var labelsByName = new HashMap<RDottedName, NPAgentLabel>();
    for (final var label : labels) {
      labelPut.execute(label);
      assertEquals(label, labelGet.execute(label.name()).orElseThrow());
      labelsByName.put(label.name(), label);
    }

    final var agent =
      new NPAgentDescription(
        new NPAgentID(UUID.randomUUID()),
        "Agent 0",
        NPKey.generate(SecureRandom.getInstanceStrong()),
        Arbitraries.maps(
          Arbitraries.strings().alpha(),
          Arbitraries.strings().alpha()
        ).sample(),
        Arbitraries.maps(
          Arbitraries.strings().alpha(),
          Arbitraries.strings().alpha()
        ).sample(),
        labelsByName
      );

    put.execute(agent);
    assertEquals(agent, get.execute(agent.id()).orElseThrow());
  }

  /**
   * Nonexistent agents are nonexistent.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAgentGet0()
    throws Exception
  {
    final var get =
      this.transaction.queries(NPDatabaseQueriesAgentsType.GetType.class);

    assertEquals(
      Optional.empty(),
      get.execute(new NPAgentID(UUID.randomUUID()))
    );
  }

  /**
   * Searching for agents works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAgentSearch0()
    throws Exception
  {
    final var get =
      this.transaction.queries(NPDatabaseQueriesAgentsType.GetType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesAgentsType.PutType.class);
    final var labelPut =
      this.transaction.queries(NPDatabaseQueriesAgentsType.LabelPutType.class);
    final var list =
      this.transaction.queries(NPDatabaseQueriesAgentsType.ListType.class);

    final var labelsByName = new HashMap<RDottedName, NPAgentLabel>();
    for (int index = 0; index <= 9; ++index) {
      final var label = new NPAgentLabel(
        new RDottedName("label%d".formatted(Integer.valueOf(index))),
        "Label %d".formatted(Integer.valueOf(index))
      );
      labelPut.execute(label);
      labelsByName.put(label.name(), label);
    }

    final ArrayList<NPAgentDescription> agents =
      generateLabelledAgents(put, labelsByName);

    {
      final var page =
        list.execute(new NPAgentListParameters(ANY_LABEL, 1000L));

      final var page0 =
        page.pageCurrent(this.transaction);

      for (final var agent : agents) {
        assertTrue(page0.items().contains(agent.summary()));
      }

      assertEquals(900, page0.items().size());
      assertEquals(1, page0.pageIndex());
    }
  }

  /**
   * Searching for agents works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAgentSearch1()
    throws Exception
  {
    final var get =
      this.transaction.queries(NPDatabaseQueriesAgentsType.GetType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesAgentsType.PutType.class);
    final var labelPut =
      this.transaction.queries(NPDatabaseQueriesAgentsType.LabelPutType.class);
    final var list =
      this.transaction.queries(NPDatabaseQueriesAgentsType.ListType.class);

    final var labelsByName = new HashMap<RDottedName, NPAgentLabel>();
    for (int index = 0; index <= 9; ++index) {
      final var label = new NPAgentLabel(
        new RDottedName("label%d".formatted(Integer.valueOf(index))),
        "Label %d".formatted(Integer.valueOf(index))
      );
      labelPut.execute(label);
      labelsByName.put(label.name(), label);
    }

    final ArrayList<NPAgentDescription> agents =
      generateLabelledAgents(put, labelsByName);

    {
      final var label0 = new RDottedName("label0");
      final var page =
        list.execute(
          new NPAgentListParameters(new Specific(label0), 1000L)
        );

      final var page0 =
        page.pageCurrent(this.transaction);

      for (final var agent : agents) {
        if (agent.labels().containsKey(label0)) {
          assertTrue(page0.items().contains(agent.summary()));
        } else {
          assertFalse(page0.items().contains(agent.summary()));
        }
      }

      assertEquals(180, page0.items().size());
      assertEquals(1, page0.pageIndex());
    }
  }

  /**
   * Searching for agents works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAgentSearch2()
    throws Exception
  {
    final var get =
      this.transaction.queries(NPDatabaseQueriesAgentsType.GetType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesAgentsType.PutType.class);
    final var labelPut =
      this.transaction.queries(NPDatabaseQueriesAgentsType.LabelPutType.class);
    final var list =
      this.transaction.queries(NPDatabaseQueriesAgentsType.ListType.class);

    final var labelsByName = new HashMap<RDottedName, NPAgentLabel>();
    for (int index = 0; index <= 9; ++index) {
      final var label = new NPAgentLabel(
        new RDottedName("label%d".formatted(Integer.valueOf(index))),
        "Label %d".formatted(Integer.valueOf(index))
      );
      labelPut.execute(label);
      labelsByName.put(label.name(), label);
    }

    final ArrayList<NPAgentDescription> agents =
      generateLabelledAgents(put, labelsByName);

    {
      final var label0 =
        new RDottedName("label0");
      final var label3 =
        new RDottedName("label3");

      final var page =
        list.execute(
          new NPAgentListParameters(
            new Or(new Specific(label0), new Specific(label3)),
            1000L)
        );

      final var page0 =
        page.pageCurrent(this.transaction);

      for (final var agent : agents) {
        final var agentLabels = agent.labels();
        if (agentLabels.containsKey(label0) || agentLabels.containsKey(label3)) {
          assertTrue(page0.items().contains(agent.summary()));
        } else {
          assertFalse(page0.items().contains(agent.summary()));
        }
      }

      assertEquals(340, page0.items().size());
      assertEquals(1, page0.pageIndex());
    }
  }

  /**
   * Searching for agents works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAgentSearch3()
    throws Exception
  {
    final var get =
      this.transaction.queries(NPDatabaseQueriesAgentsType.GetType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesAgentsType.PutType.class);
    final var labelPut =
      this.transaction.queries(NPDatabaseQueriesAgentsType.LabelPutType.class);
    final var list =
      this.transaction.queries(NPDatabaseQueriesAgentsType.ListType.class);

    final var labelsByName = new HashMap<RDottedName, NPAgentLabel>();
    for (int index = 0; index <= 9; ++index) {
      final var label = new NPAgentLabel(
        new RDottedName("label%d".formatted(Integer.valueOf(index))),
        "Label %d".formatted(Integer.valueOf(index))
      );
      labelPut.execute(label);
      labelsByName.put(label.name(), label);
    }

    final ArrayList<NPAgentDescription> agents =
      generateLabelledAgents(put, labelsByName);

    {
      final var label0 =
        new RDottedName("label0");
      final var label3 =
        new RDottedName("label3");

      final var page =
        list.execute(
          new NPAgentListParameters(
            new And(new Specific(label0), new Specific(label3)),
            1000L)
        );

      final var page0 =
        page.pageCurrent(this.transaction);

      for (final var agent : agents) {
        final var agentLabels = agent.labels();
        if (agentLabels.containsKey(label0) && agentLabels.containsKey(label3)) {
          assertTrue(page0.items().contains(agent.summary()));
        } else {
          assertFalse(page0.items().contains(agent.summary()));
        }
      }

      assertEquals(20, page0.items().size());
      assertEquals(1, page0.pageIndex());
    }
  }

  private static ArrayList<NPAgentDescription> generateLabelledAgents(
    final NPDatabaseQueriesAgentsType.PutType put,
    final HashMap<RDottedName, NPAgentLabel> labelsByName)
    throws NoSuchAlgorithmException, NPDatabaseException
  {
    final var agents = new ArrayList<NPAgentDescription>();
    for (int index = 0; index <= 899; ++index) {
      final var name0 =
        new RDottedName("label%d".formatted(Integer.valueOf(index % 10)));
      final var name1 =
        new RDottedName("label%d".formatted(Integer.valueOf(index / 100)));

      final var agentLabels = new HashMap<RDottedName, NPAgentLabel>();
      agentLabels.put(name0, labelsByName.get(name0));
      agentLabels.put(name1, labelsByName.get(name1));

      final var agent =
        new NPAgentDescription(
          new NPAgentID(UUID.randomUUID()),
          "Agent %d".formatted(Integer.valueOf(index)),
          NPKey.generate(SecureRandom.getInstanceStrong()),
          Map.of(),
          Map.of(),
          agentLabels
        );

      put.execute(agent);
      agents.add(agent);
    }
    return agents;
  }

  /**
   * Retrieving an agent by key works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAgentGetByKey0()
    throws Exception
  {
    final var get =
      this.transaction.queries(NPDatabaseQueriesAgentsType.GetByKeyType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesAgentsType.PutType.class);

    final var agent =
      new NPAgentDescription(
        new NPAgentID(UUID.randomUUID()),
        "Agent 0",
        NPKey.generate(SecureRandom.getInstanceStrong()),
        Map.of(),
        Map.of(),
        Map.of()
      );

    put.execute(agent);
    this.transaction.commit();

    assertEquals(agent, get.execute(agent.accessKey()).orElseThrow());
  }

  /**
   * Retrieving an agent by works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAgentGet1()
    throws Exception
  {
    final var get =
      this.transaction.queries(NPDatabaseQueriesAgentsType.GetType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesAgentsType.PutType.class);

    final var agent =
      new NPAgentDescription(
        new NPAgentID(UUID.randomUUID()),
        "Agent 0",
        NPKey.generate(SecureRandom.getInstanceStrong()),
        Map.of(),
        Map.of(),
        Map.of()
      );

    put.execute(agent);
    this.transaction.commit();

    assertEquals(agent, get.execute(agent.id()).orElseThrow());
  }

  /**
   * Searching for labels works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAgentLabelSearch0()
    throws Exception
  {
    final var labelPut =
      this.transaction.queries(NPDatabaseQueriesAgentsType.LabelPutType.class);
    final var labelSearch =
      this.transaction.queries(NPDatabaseQueriesAgentsType.LabelSearchType.class);

    final var labelsByName = new HashMap<RDottedName, NPAgentLabel>();
    for (int index = 0; index < 1000; ++index) {
      final var name = new RDottedName("drawer.abacus" + index);
      final var label = new NPAgentLabel(name, "Drawer Abacus " + index);
      labelPut.execute(label);
      labelsByName.put(name, label);
    }

    this.transaction.commit();

    final var paged =
      labelSearch.execute(new NPAgentLabelSearchParameters("abacus"));

    final var labelsByNameRetrieved =
      new HashMap<RDottedName, NPAgentLabel>();

    for (int index = 0; index < 10; ++index) {
      final var page =
        paged.pageCurrent(this.transaction);

      for (final var item : page.items()) {
        labelsByNameRetrieved.put(item.name(), item);
      }

      paged.pageNext(this.transaction);
    }

    assertEquals(labelsByName, labelsByNameRetrieved);
  }

  /**
   * Searching for labels works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAgentLabelSearch1()
    throws Exception
  {
    final var labelPut =
      this.transaction.queries(NPDatabaseQueriesAgentsType.LabelPutType.class);
    final var labelSearch =
      this.transaction.queries(NPDatabaseQueriesAgentsType.LabelSearchType.class);

    final var labelsByName = new HashMap<RDottedName, NPAgentLabel>();
    for (int index = 0; index < 1000; ++index) {
      final var name = new RDottedName("drawer.abacus" + index);
      final var label = new NPAgentLabel(name, "Drawer Abacus " + index);
      labelPut.execute(label);
      labelsByName.put(name, label);
    }

    this.transaction.commit();

    final var paged =
      labelSearch.execute(new NPAgentLabelSearchParameters(""));

    final var labelsByNameRetrieved =
      new HashMap<RDottedName, NPAgentLabel>();

    for (int index = 0; index < 10; ++index) {
      final var page =
        paged.pageCurrent(this.transaction);

      for (final var item : page.items()) {
        labelsByNameRetrieved.put(item.name(), item);
      }

      paged.pageNext(this.transaction);
    }

    assertEquals(labelsByName, labelsByNameRetrieved);
  }

  /**
   * Deleting labels works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAgentLabelDelete()
    throws Exception
  {
    final var get =
      this.transaction.queries(NPDatabaseQueriesAgentsType.GetType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesAgentsType.PutType.class);
    final var labelPut =
      this.transaction.queries(NPDatabaseQueriesAgentsType.LabelPutType.class);
    final var labelDelete =
      this.transaction.queries(NPDatabaseQueriesAgentsType.LabelDeleteType.class);

    final var labels =
      Arbitraries.defaultFor(NPAgentLabel.class)
        .set()
        .ofSize(100)
        .sample();

    final var byName = new HashMap<RDottedName, NPAgentLabel>();
    for (final var label : labels) {
      labelPut.execute(label);
      byName.put(label.name(), label);
    }

    final var agent0 =
      new NPAgentDescription(
        new NPAgentID(UUID.randomUUID()),
        "Agent 0",
        NPKey.generate(SecureRandom.getInstanceStrong()),
        Map.of(),
        Map.of(),
        byName
      );

    put.execute(agent0);
    this.transaction.commit();

    labelDelete.execute(
      labels.stream()
        .map(NPAgentLabel::name)
        .collect(Collectors.toUnmodifiableSet())
    );

    final var agent1 =
      new NPAgentDescription(
        agent0.id(),
        agent0.name(),
        agent0.accessKey(),
        Map.of(),
        Map.of(),
        Map.of()
      );

    assertEquals(agent1, get.execute(agent0.id()).orElseThrow());
  }
}
