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
import com.io7m.northpike.database.api.NPDatabaseConnectionType;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.model.agents.NPAgentDescription;
import com.io7m.northpike.model.agents.NPAgentID;
import com.io7m.northpike.model.agents.NPAgentKeyPairFactoryEd448;
import com.io7m.northpike.model.agents.NPAgentKeyPublicType;
import com.io7m.northpike.model.agents.NPAgentLabel;
import com.io7m.northpike.model.agents.NPAgentLabelName;
import com.io7m.northpike.model.agents.NPAgentLabelSearchParameters;
import com.io7m.northpike.model.agents.NPAgentLoginChallenge;
import com.io7m.northpike.model.agents.NPAgentLoginChallengeRecord;
import com.io7m.northpike.model.agents.NPAgentSearchParameters;
import com.io7m.northpike.model.agents.NPAgentSummary;
import com.io7m.northpike.model.comparisons.NPComparisonFuzzyType;
import com.io7m.northpike.model.comparisons.NPComparisonSetType.Anything;
import com.io7m.northpike.model.comparisons.NPComparisonSetType.IsEqualTo;
import com.io7m.northpike.model.comparisons.NPComparisonSetType.IsSubsetOf;
import com.io7m.northpike.model.comparisons.NPComparisonSetType.IsSupersetOf;
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

import java.nio.charset.StandardCharsets;
import java.time.OffsetDateTime;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;
import java.util.function.Function;
import java.util.stream.Collectors;

import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
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

    this.transaction.setOwner(
      NPTestContainers.NPDatabaseFixture.createUser(
        this.transaction,
        UUID.randomUUID()
      )
    );
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

    final var labelsByName = new HashMap<NPAgentLabelName, NPAgentLabel>();
    for (final var label : labels) {
      labelPut.execute(label);
      assertEquals(label, labelGet.execute(label.name()).orElseThrow());
      labelsByName.put(label.name(), label);
    }

    final var agent =
      new NPAgentDescription(
        new NPAgentID(UUID.randomUUID()),
        "Agent 0",
        Arbitraries.defaultFor(NPAgentKeyPublicType.class)
          .sample(),
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

    final var labelsByName = new HashMap<NPAgentLabelName, NPAgentLabel>();
    for (final var label : labels) {
      labelPut.execute(label);
      assertEquals(label, labelGet.execute(label.name()).orElseThrow());
      labelsByName.put(label.name(), label);
    }

    final var agent =
      new NPAgentDescription(
        new NPAgentID(UUID.randomUUID()),
        "Agent 0",
        Arbitraries.defaultFor(NPAgentKeyPublicType.class)
          .sample(),
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
    final var put =
      this.transaction.queries(NPDatabaseQueriesAgentsType.PutType.class);
    final var labelPut =
      this.transaction.queries(NPDatabaseQueriesAgentsType.LabelPutType.class);
    final var list =
      this.transaction.queries(NPDatabaseQueriesAgentsType.ListType.class);

    final var labelsByName = new HashMap<NPAgentLabelName, NPAgentLabel>();
    for (int index = 0; index <= 9; ++index) {
      final var label = new NPAgentLabel(
        NPAgentLabelName.of("label%d".formatted(Integer.valueOf(index))),
        "Label %d".formatted(Integer.valueOf(index))
      );
      labelPut.execute(label);
      labelsByName.put(label.name(), label);
    }

    final Map<NPAgentID, NPAgentDescription> agents =
      generateLabelledAgents(put, labelsByName);

    {
      final var page =
        list.execute(new NPAgentSearchParameters(new Anything<>(), 1000L));

      final var page0 =
        page.pageCurrent(this.transaction);

      final var pageAgents =
        page0.items()
          .stream()
          .collect(Collectors.toMap(NPAgentSummary::id, Function.identity()));

      /*
       * The returned agents are all the agents.
       */

      for (final var agent : agents.values()) {
        assertTrue(pageAgents.containsKey(agent.id()));
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
    final var put =
      this.transaction.queries(NPDatabaseQueriesAgentsType.PutType.class);
    final var labelPut =
      this.transaction.queries(NPDatabaseQueriesAgentsType.LabelPutType.class);
    final var list =
      this.transaction.queries(NPDatabaseQueriesAgentsType.ListType.class);

    final var labelsByName = new HashMap<NPAgentLabelName, NPAgentLabel>();
    for (int index = 0; index <= 9; ++index) {
      final var label = new NPAgentLabel(
        NPAgentLabelName.of("label%d".formatted(Integer.valueOf(index))),
        "Label %d".formatted(Integer.valueOf(index))
      );
      labelPut.execute(label);
      labelsByName.put(label.name(), label);
    }

    final Map<NPAgentID, NPAgentDescription> agents =
      generateLabelledAgents(put, labelsByName);

    {
      final var label0 =
        NPAgentLabelName.of("label0");

      final var page =
        list.execute(
          new NPAgentSearchParameters(
            new IsEqualTo<>(Set.of(label0)), 1000L)
        );

      final var page0 =
        page.pageCurrent(this.transaction);

      final var pageAgents =
        page0.items()
          .stream()
          .collect(Collectors.toMap(NPAgentSummary::id, Function.identity()));

      /*
       * The returned agents are those that have the exact label set.
       */

      for (final var pageAgent : pageAgents.values()) {
        final var agent = agents.get(pageAgent.id());
        assertEquals(
          Set.of(label0),
          Set.copyOf(agent.labels().keySet())
        );
      }

      assertEquals(10, pageAgents.size());
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
    final var put =
      this.transaction.queries(NPDatabaseQueriesAgentsType.PutType.class);
    final var labelPut =
      this.transaction.queries(NPDatabaseQueriesAgentsType.LabelPutType.class);
    final var list =
      this.transaction.queries(NPDatabaseQueriesAgentsType.ListType.class);

    final var labelsByName = new HashMap<NPAgentLabelName, NPAgentLabel>();
    for (int index = 0; index <= 9; ++index) {
      final var label = new NPAgentLabel(
        NPAgentLabelName.of("label%d".formatted(Integer.valueOf(index))),
        "Label %d".formatted(Integer.valueOf(index))
      );
      labelPut.execute(label);
      labelsByName.put(label.name(), label);
    }

    final Map<NPAgentID, NPAgentDescription> agents =
      generateLabelledAgents(put, labelsByName);

    {
      final var label0 =
        NPAgentLabelName.of("label0");
      final var label3 =
        NPAgentLabelName.of("label3");

      final var page =
        list.execute(
          new NPAgentSearchParameters(
            new IsSubsetOf<>(Set.of(label0, label3)),
            1000L)
        );

      final var page0 =
        page.pageCurrent(this.transaction);

      final var pageAgents =
        page0.items()
          .stream()
          .collect(Collectors.toMap(NPAgentSummary::id, Function.identity()));

      /*
       * The returned agents are those that have a subset of the given labels
       */

      for (final var agent : pageAgents.values()) {
        final var original =
          agents.get(agent.id());
        final var originalLabels =
          original.labels().keySet();

        var ok =
          Objects.equals(originalLabels, Set.<NPAgentLabelName>of());
        ok = ok || originalLabels.equals(Set.of(label0));
        ok = ok || originalLabels.equals(Set.of(label3));
        ok = ok || originalLabels.equals(Set.of(label0, label3));

        assertTrue(
          ok,
          "Agent labels %s must be a subset of %s"
            .formatted(originalLabels, Set.of(label0, label3))
        );
      }

      assertEquals(40, page0.items().size());
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
    final var put =
      this.transaction.queries(NPDatabaseQueriesAgentsType.PutType.class);
    final var labelPut =
      this.transaction.queries(NPDatabaseQueriesAgentsType.LabelPutType.class);
    final var list =
      this.transaction.queries(NPDatabaseQueriesAgentsType.ListType.class);

    final var labelsByName = new HashMap<NPAgentLabelName, NPAgentLabel>();
    for (int index = 0; index <= 9; ++index) {
      final var label = new NPAgentLabel(
        NPAgentLabelName.of("label%d".formatted(Integer.valueOf(index))),
        "Label %d".formatted(Integer.valueOf(index))
      );
      labelPut.execute(label);
      labelsByName.put(label.name(), label);
    }

    final Map<NPAgentID, NPAgentDescription> agents =
      generateLabelledAgents(put, labelsByName);

    {
      final var label0 =
        NPAgentLabelName.of("label0");
      final var label3 =
        NPAgentLabelName.of("label3");

      final var page =
        list.execute(
          new NPAgentSearchParameters(
            new IsSupersetOf<>(Set.of(label0, label3)),
            1000L)
        );

      final var page0 =
        page.pageCurrent(this.transaction);

      final var pageAgents =
        page0.items()
          .stream()
          .collect(Collectors.toMap(NPAgentSummary::id, Function.identity()));

      /*
       * The returned agents are those that have a superset of the given labels
       */

      for (final var agent : pageAgents.values()) {
        final var original =
          agents.get(agent.id());
        final var originalLabels =
          original.labels().keySet();

        assertTrue(originalLabels.contains(label0));
        assertTrue(originalLabels.contains(label3));
      }

      assertEquals(20, page0.items().size());
      assertEquals(1, page0.pageIndex());
    }
  }

  /**
   * Deleted agents don't appear in searches.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAgentSearchDeleted0()
    throws Exception
  {
    final var delete =
      this.transaction.queries(NPDatabaseQueriesAgentsType.DeleteType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesAgentsType.PutType.class);
    final var labelPut =
      this.transaction.queries(NPDatabaseQueriesAgentsType.LabelPutType.class);
    final var list =
      this.transaction.queries(NPDatabaseQueriesAgentsType.ListType.class);

    final var labelsByName = new HashMap<NPAgentLabelName, NPAgentLabel>();
    for (int index = 0; index <= 9; ++index) {
      final var label = new NPAgentLabel(
        NPAgentLabelName.of("label%d".formatted(Integer.valueOf(index))),
        "Label %d".formatted(Integer.valueOf(index))
      );
      labelPut.execute(label);
      labelsByName.put(label.name(), label);
    }

    final Map<NPAgentID, NPAgentDescription> agents =
      generateLabelledAgents(put, labelsByName);

    final var deleted =
      new HashSet<NPAgentID>();

    int index = 0;
    for (final var agent : agents.values()) {
      if (index % 2 == 0) {
        delete.execute(agent.id());
        deleted.add(agent.id());
      }
      ++index;
    }

    {
      final var page =
        list.execute(new NPAgentSearchParameters(
          new Anything<>(),
          1000L)
        );

      final var page0 =
        page.pageCurrent(this.transaction);

      for (final var agent : page0.items()) {
        assertFalse(deleted.contains(agent.id()));
      }

      assertEquals(450, page0.items().size());
      assertEquals(1, page0.pageIndex());
    }
  }


  private static Map<NPAgentID, NPAgentDescription> generateLabelledAgents(
    final NPDatabaseQueriesAgentsType.PutType put,
    final HashMap<NPAgentLabelName, NPAgentLabel> labelsByName)
    throws NPDatabaseException
  {
    final var agents = new HashMap<NPAgentID, NPAgentDescription>();
    for (int index = 0; index <= 899; ++index) {
      final var name0 =
        NPAgentLabelName.of("label%d".formatted(Integer.valueOf(index % 10)));
      final var name1 =
        NPAgentLabelName.of("label%d".formatted(Integer.valueOf(index / 100)));

      final var agentLabels = new HashMap<NPAgentLabelName, NPAgentLabel>();
      agentLabels.put(name0, labelsByName.get(name0));
      agentLabels.put(name1, labelsByName.get(name1));

      final var agent =
        new NPAgentDescription(
          new NPAgentID(UUID.randomUUID()),
          "Agent %d".formatted(Integer.valueOf(index)),
          Arbitraries.defaultFor(NPAgentKeyPublicType.class)
            .sample(),
          Map.of(),
          Map.of(),
          agentLabels
        );

      put.execute(agent);
      agents.put(agent.id(), agent);
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

    final var key =
      Arbitraries.defaultFor(NPAgentKeyPublicType.class)
      .sample();

    final var agent =
      new NPAgentDescription(
        new NPAgentID(UUID.randomUUID()),
        "Agent 0",
        key,
        Map.of(),
        Map.of(),
        Map.of()
      );

    put.execute(agent);
    this.transaction.commit();

    assertEquals(agent, get.execute(key).orElseThrow());
  }

  /**
   * Retrieving an agent by id works.
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
        Arbitraries.defaultFor(NPAgentKeyPublicType.class)
          .sample(),
        Map.of(),
        Map.of(),
        Map.of()
      );

    put.execute(agent);
    this.transaction.commit();

    assertEquals(agent, get.execute(agent.id()).orElseThrow());
  }

  /**
   * Deleted agents can't be retrieved.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAgentGetDeleted()
    throws Exception
  {
    final var get =
      this.transaction.queries(NPDatabaseQueriesAgentsType.GetType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesAgentsType.PutType.class);
    final var delete =
      this.transaction.queries(NPDatabaseQueriesAgentsType.DeleteType.class);

    final var agent =
      new NPAgentDescription(
        new NPAgentID(UUID.randomUUID()),
        "Agent 0",
        Arbitraries.defaultFor(NPAgentKeyPublicType.class)
          .sample(),
        Map.of(),
        Map.of(),
        Map.of()
      );

    put.execute(agent);
    this.transaction.commit();

    delete.execute(agent.id());
    assertEquals(Optional.empty(), get.execute(agent.id()));
  }

  /**
   * The access keys of deleted agents are no longer unique.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAgentGetDeletedAccessUnique()
    throws Exception
  {
    final var get =
      this.transaction.queries(NPDatabaseQueriesAgentsType.GetByKeyType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesAgentsType.PutType.class);
    final var delete =
      this.transaction.queries(NPDatabaseQueriesAgentsType.DeleteType.class);

    final NPAgentKeyPublicType key =
      Arbitraries.defaultFor(NPAgentKeyPublicType.class)
        .sample();

    final var agent0 =
      new NPAgentDescription(
        new NPAgentID(UUID.randomUUID()),
        "Agent 0",
        key,
        Map.of(),
        Map.of(),
        Map.of()
      );

    final var agent1 =
      new NPAgentDescription(
        new NPAgentID(UUID.randomUUID()),
        "Agent 0",
        key,
        Map.of(),
        Map.of(),
        Map.of()
      );

    put.execute(agent0);

    final var ex =
      assertThrows(NPDatabaseException.class, () -> put.execute(agent1));
    assertEquals(NPStandardErrorCodes.errorDuplicate(), ex.errorCode());

    delete.execute(agent0.id());
    put.execute(agent1);

    assertEquals(agent1, get.execute(key).orElseThrow());
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

    final var labelsByName = new HashMap<NPAgentLabelName, NPAgentLabel>();
    for (int index = 0; index < 1000; ++index) {
      final var name = NPAgentLabelName.of("drawer.abacus" + index);
      final var label = new NPAgentLabel(name, "Drawer Abacus " + index);
      labelPut.execute(label);
      labelsByName.put(name, label);
    }

    this.transaction.commit();

    final var paged =
      labelSearch.execute(
        new NPAgentLabelSearchParameters(
          new NPComparisonFuzzyType.IsSimilarTo<>("abacus3"),
          new NPComparisonFuzzyType.Anything<>(),
          1000L
        )
      );

    final var labelsByNameRetrieved =
      new HashMap<NPAgentLabelName, NPAgentLabel>();

    for (int index = 0; index < 10; ++index) {
      final var page =
        paged.pageCurrent(this.transaction);

      for (final var item : page.items()) {
        labelsByNameRetrieved.put(item.name(), item);
      }

      paged.pageNext(this.transaction);
    }

    assertEquals(Map.of(
      NPAgentLabelName.of("drawer.abacus3"),
      new NPAgentLabel(
        NPAgentLabelName.of("drawer.abacus3"),
        "Drawer Abacus 3"
      )
    ), labelsByNameRetrieved);
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

    final var labelsByName = new HashMap<NPAgentLabelName, NPAgentLabel>();
    for (int index = 0; index < 1000; ++index) {
      final var name = NPAgentLabelName.of("drawer.abacus" + index);
      final var label = new NPAgentLabel(name, "Drawer Abacus " + index);
      labelPut.execute(label);
      labelsByName.put(name, label);
    }

    this.transaction.commit();

    final var paged =
      labelSearch.execute(
        new NPAgentLabelSearchParameters(
          new NPComparisonFuzzyType.Anything<>(),
          new NPComparisonFuzzyType.IsSimilarTo<>("abacus"),
          1000L
        )
      );

    final var labelsByNameRetrieved =
      new HashMap<NPAgentLabelName, NPAgentLabel>();

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

    final var byName = new HashMap<NPAgentLabelName, NPAgentLabel>();
    for (final var label : labels) {
      labelPut.execute(label);
      byName.put(label.name(), label);
    }

    final var agent0 =
      new NPAgentDescription(
        new NPAgentID(UUID.randomUUID()),
        "Agent 0",
        Arbitraries.defaultFor(NPAgentKeyPublicType.class)
          .sample(),
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
        agent0.publicKey(),
        Map.of(),
        Map.of(),
        Map.of()
      );

    assertEquals(agent1, get.execute(agent0.id()).orElseThrow());
  }

  /**
   * Manipulating login challenges works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAgentLoginChallenges()
    throws Exception
  {
    final var get =
      this.transaction.queries(NPDatabaseQueriesAgentsType.LoginChallengeGetType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesAgentsType.LoginChallengePutType.class);
    final var delete =
      this.transaction.queries(NPDatabaseQueriesAgentsType.LoginChallengeDeleteType.class);

    final var record0 =
      new NPAgentLoginChallengeRecord(
        OffsetDateTime.now().withNano(0),
        "localhost",
        new NPAgentKeyPairFactoryEd448().generateKeyPair().publicKey(),
        new NPAgentLoginChallenge(
          UUID.randomUUID(),
          "ABCDEFGH".getBytes(StandardCharsets.UTF_8)
        )
      );

    put.execute(record0);
    assertEquals(record0, get.execute(record0.id()).orElseThrow());
    put.execute(record0);
    assertEquals(record0, get.execute(record0.id()).orElseThrow());
    delete.execute(record0.id());
    assertEquals(Optional.empty(), get.execute(record0.id()));
  }
}
