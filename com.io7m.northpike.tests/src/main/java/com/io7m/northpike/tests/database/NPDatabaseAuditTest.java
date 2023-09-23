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
import com.io7m.idstore.model.IdName;
import com.io7m.medrina.api.MSubject;
import com.io7m.northpike.database.api.NPDatabaseConnectionType;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesAuditType;
import com.io7m.northpike.database.api.NPDatabaseQueriesUsersType;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.model.NPAuditEvent;
import com.io7m.northpike.model.NPAuditSearchParameters;
import com.io7m.northpike.model.NPTimeRange;
import com.io7m.northpike.model.NPUser;
import com.io7m.northpike.tests.containers.NPTestContainerInstances;
import com.io7m.northpike.tests.containers.NPTestContainers;
import com.io7m.zelador.test_extension.CloseableResourcesType;
import com.io7m.zelador.test_extension.ZeladorExtension;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;

import java.time.OffsetDateTime;
import java.util.ArrayList;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;

import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE;
import static org.junit.jupiter.api.Assertions.assertEquals;

@ExtendWith({ErvillaExtension.class, ZeladorExtension.class})
@ErvillaConfiguration(projectName = "com.io7m.northpike", disabledIfUnsupported = true)
public final class NPDatabaseAuditTest
{
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
   * Searching for audit events works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAuditSearch0()
    throws Exception
  {
    final var userPut =
      this.transaction.queries(NPDatabaseQueriesUsersType.PutType.class);
    final var add =
      this.transaction.queries(NPDatabaseQueriesAuditType.EventAddType.class);
    final var search =
      this.transaction.queries(NPDatabaseQueriesAuditType.EventSearchType.class);

    final ArrayList<NPUser> users =
      createTestUsers(userPut);

    final ArrayList<NPAuditEvent> events =
      generateEvents(users, add);

    {
      final var page =
        search.execute(
          new NPAuditSearchParameters(
            Optional.empty(),
            Optional.empty(),
            NPTimeRange.largest(),
            1000L
          )
        );

      final var page0 =
        page.pageCurrent(this.transaction);

      assertEquals(900, page0.items().size());
      assertEquals(1, page0.pageIndex());
    }
  }

  /**
   * Searching for audit events works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAuditSearch1()
    throws Exception
  {
    final var userPut =
      this.transaction.queries(NPDatabaseQueriesUsersType.PutType.class);
    final var add =
      this.transaction.queries(NPDatabaseQueriesAuditType.EventAddType.class);
    final var search =
      this.transaction.queries(NPDatabaseQueriesAuditType.EventSearchType.class);

    final ArrayList<NPUser> users =
      createTestUsers(userPut);

    final ArrayList<NPAuditEvent> events =
      generateEvents(users, add);

    {
      final var page =
        search.execute(
          new NPAuditSearchParameters(
            Optional.of(users.get(0).userId()),
            Optional.empty(),
            NPTimeRange.largest(),
            1000L
          )
        );

      final var page0 =
        page.pageCurrent(this.transaction);

      assertEquals(180, page0.items().size());
      assertEquals(1, page0.pageIndex());
    }
  }

  /**
   * Searching for audit events works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAuditSearch2()
    throws Exception
  {
    final var userPut =
      this.transaction.queries(NPDatabaseQueriesUsersType.PutType.class);
    final var add =
      this.transaction.queries(NPDatabaseQueriesAuditType.EventAddType.class);
    final var search =
      this.transaction.queries(NPDatabaseQueriesAuditType.EventSearchType.class);

    final ArrayList<NPUser> users =
      createTestUsers(userPut);

    final ArrayList<NPAuditEvent> events =
      generateEvents(users, add);

    {
      final var page =
        search.execute(
          new NPAuditSearchParameters(
            Optional.empty(),
            Optional.of("TYPE_2"),
            NPTimeRange.largest(),
            1000L
          )
        );

      final var page0 =
        page.pageCurrent(this.transaction);

      assertEquals(100, page0.items().size());
      assertEquals(1, page0.pageIndex());
    }
  }

  /**
   * Searching for audit events works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAuditSearch3()
    throws Exception
  {
    final var userPut =
      this.transaction.queries(NPDatabaseQueriesUsersType.PutType.class);
    final var add =
      this.transaction.queries(NPDatabaseQueriesAuditType.EventAddType.class);
    final var search =
      this.transaction.queries(NPDatabaseQueriesAuditType.EventSearchType.class);

    final ArrayList<NPUser> users =
      createTestUsers(userPut);

    final ArrayList<NPAuditEvent> events =
      generateEvents(users, add);

    {
      final var page =
        search.execute(
          new NPAuditSearchParameters(
            Optional.empty(),
            Optional.empty(),
            new NPTimeRange(
              events.get(0).time(),
              events.get(99).time()
            ),
            1000L
          )
        );

      final var page0 =
        page.pageCurrent(this.transaction);

      assertEquals(100, page0.items().size());
      assertEquals(1, page0.pageIndex());
      assertEquals(events.get(0), page0.items().get(0));
      assertEquals(events.get(99), page0.items().get(99));
    }
  }

  private static ArrayList<NPUser> createTestUsers(
    final NPDatabaseQueriesUsersType.PutType userPut)
    throws NPDatabaseException
  {
    final var users = new ArrayList<NPUser>();
    users.add(
      new NPUser(
        UUID.randomUUID(),
        new IdName("example-1"),
        new MSubject(Set.of())
      )
    );
    users.add(
      new NPUser(
        UUID.randomUUID(),
        new IdName("example-2"),
        new MSubject(Set.of())
      )
    );
    users.add(
      new NPUser(
        UUID.randomUUID(),
        new IdName("example-3"),
        new MSubject(Set.of())
      )
    );
    users.add(
      new NPUser(
        UUID.randomUUID(),
        new IdName("example-4"),
        new MSubject(Set.of())
      )
    );
    users.add(
      new NPUser(
        UUID.randomUUID(),
        new IdName("example-5"),
        new MSubject(Set.of())
      )
    );
    for (final var user : users) {
      userPut.execute(user);
    }
    return users;
  }

  private static ArrayList<NPAuditEvent> generateEvents(
    final ArrayList<NPUser> users,
    final NPDatabaseQueriesAuditType.EventAddType put)
    throws NPDatabaseException
  {
    final var events = new ArrayList<NPAuditEvent>();

    final var timeStart =
      OffsetDateTime.now()
        .withNano(0)
        .minusSeconds(100L);

    var sum = 0;
    for (int index = 0; index <= 899; ++index) {
      sum = sum + index;

      final var user =
        users.get(index % users.size());

      final var agent =
        new NPAuditEvent(
          timeStart.plusSeconds(index),
          user.userId(),
          "TYPE_" + index / 100,
          Map.ofEntries(
            Map.entry("INDEX", Integer.toUnsignedString(index)),
            Map.entry("SUM", Integer.toUnsignedString(sum))
          )
        );

      put.execute(agent);
      events.add(agent);
    }
    return events;
  }

}
