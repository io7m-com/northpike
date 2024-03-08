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
import com.io7m.lanark.core.RDottedName;
import com.io7m.medrina.api.MRoleName;
import com.io7m.medrina.api.MSubject;
import com.io7m.northpike.database.api.NPDatabaseConnectionType;
import com.io7m.northpike.database.api.NPDatabaseQueriesMaintenanceType;
import com.io7m.northpike.database.api.NPDatabaseQueriesUsersType;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.database.api.NPDatabaseUnit;
import com.io7m.northpike.model.NPAuditUserOrAgentType.User;
import com.io7m.northpike.model.NPUser;
import com.io7m.northpike.model.NPUserSearchParameters;
import com.io7m.northpike.model.comparisons.NPComparisonFuzzyType;
import com.io7m.northpike.model.comparisons.NPComparisonSetType;
import com.io7m.northpike.model.security.NPSecRole;
import com.io7m.northpike.tests.containers.NPDatabaseFixture;
import com.io7m.northpike.tests.containers.NPFixtures;
import com.io7m.zelador.test_extension.CloseableResourcesType;
import com.io7m.zelador.test_extension.ZeladorExtension;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.junit.jupiter.api.function.Executable;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;
import java.util.stream.Collectors;

import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE;
import static com.io7m.northpike.model.security.NPSecRole.ADMINISTRATOR;
import static com.io7m.northpike.model.security.NPSecRole.LOGIN;
import static com.io7m.northpike.model.security.NPSecRole.allRoles;
import static org.junit.jupiter.api.Assertions.assertAll;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

@ExtendWith({ErvillaExtension.class, ZeladorExtension.class})
@ErvillaConfiguration(projectName = "com.io7m.northpike", disabledIfUnsupported = true)
public final class NPDatabaseUsersTest
{
  private static NPDatabaseFixture DATABASE_FIXTURE;
  private NPDatabaseConnectionType connection;
  private NPDatabaseTransactionType transaction;
  private NPDatabaseType database;

  @BeforeAll
  public static void setupOnce(
    final @ErvillaCloseAfterSuite EContainerSupervisorType containers)
    throws Exception
  {
    DATABASE_FIXTURE = NPFixtures.database(containers);
  }

  @BeforeEach
  public void setup(
    final @ErvillaCloseAfterSuite EContainerSupervisorType containers,
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
      DATABASE_FIXTURE.userSetup(NPFixtures.idstore(containers).userWithLogin())
    );
  }

  /**
   * Creating users works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testUserCreate0()
    throws Exception
  {
    final var get =
      this.transaction.queries(NPDatabaseQueriesUsersType.GetType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesUsersType.PutType.class);

    final var user =
      new NPUser(
        UUID.randomUUID(),
        new IdName("x"),
        new MSubject(Set.of())
      );

    this.transaction.setOwner(new User(user.userId()));
    put.execute(user);
    assertEquals(user, get.execute(user.userId()).orElseThrow());
  }

  /**
   * Creating users works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testUserCreate1()
    throws Exception
  {
    final var get =
      this.transaction.queries(NPDatabaseQueriesUsersType.GetType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesUsersType.PutType.class);

    final var user =
      new NPUser(
        UUID.randomUUID(),
        new IdName("x"),
        new MSubject(Set.of(
          MRoleName.of("role0"),
          MRoleName.of("role1"),
          MRoleName.of("role2")
        ))
      );

    this.transaction.setOwner(new User(user.userId()));
    put.execute(user);
    assertEquals(user, get.execute(user.userId()).orElseThrow());
  }

  /**
   * Nonexistent users are nonexistent.
   *
   * @throws Exception On errors
   */

  @Test
  public void testUserGet0()
    throws Exception
  {
    final var get =
      this.transaction.queries(NPDatabaseQueriesUsersType.GetType.class);

    assertEquals(Optional.empty(), get.execute(UUID.randomUUID()));
  }

  /**
   * Maintenance will fix the roles of users.
   *
   * @throws Exception On errors
   */

  @Test
  public void testUserAdminMaintenance0()
    throws Exception
  {
    final var get =
      this.transaction.queries(NPDatabaseQueriesUsersType.GetType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesUsersType.PutType.class);
    final var maintenance =
      this.transaction.queries(NPDatabaseQueriesMaintenanceType.UpdateUserRolesType.class);

    final var user =
      new NPUser(
        UUID.randomUUID(),
        new IdName("x"),
        new MSubject(Set.of(ADMINISTRATOR.role(), LOGIN.role()))
      );

    final var userWithAllRoles =
      new NPUser(
        user.userId(),
        user.name(),
        new MSubject(
          allRoles()
            .stream()
            .map(NPSecRole::role)
            .collect(Collectors.toUnmodifiableSet())
        )
      );

    this.transaction.setOwner(new User(user.userId()));
    put.execute(user);
    maintenance.execute(NPDatabaseUnit.UNIT);

    assertEquals(userWithAllRoles, get.execute(user.userId()).orElseThrow());
  }

  /**
   * Maintenance will ignore users that do not have the LOGIN role.
   *
   * @throws Exception On errors
   */

  @Test
  public void testUserAdminMaintenance1()
    throws Exception
  {
    final var get =
      this.transaction.queries(NPDatabaseQueriesUsersType.GetType.class);
    final var put =
      this.transaction.queries(NPDatabaseQueriesUsersType.PutType.class);
    final var maintenance =
      this.transaction.queries(NPDatabaseQueriesMaintenanceType.UpdateUserRolesType.class);

    final var user =
      new NPUser(
        UUID.randomUUID(),
        new IdName("x"),
        new MSubject(Set.of(ADMINISTRATOR.role()))
      );

    this.transaction.setOwner(new User(user.userId()));
    put.execute(user);
    maintenance.execute(NPDatabaseUnit.UNIT);

    assertEquals(user, get.execute(user.userId()).orElseThrow());
  }

  /**
   * Searching for users works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testUserSearch0()
    throws Exception
  {
    final var put =
      this.transaction.queries(NPDatabaseQueriesUsersType.PutType.class);
    final var search =
      this.transaction.queries(NPDatabaseQueriesUsersType.SearchType.class);

    final var users = generateUsers();
    for (final var u : users) {
      put.execute(u);
    }

    this.transaction.commit();

    final var params =
      new NPUserSearchParameters(
        new NPComparisonFuzzyType.Anything<>(),
        new NPComparisonSetType.Anything<>(),
        1000L
      );

    final var paged = search.execute(params);
    final var page = paged.pageCurrent(this.transaction);

    checkSameSets(users, page.items());
  }

  /**
   * Searching for users works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testUserSearch1()
    throws Exception
  {
    final var put =
      this.transaction.queries(NPDatabaseQueriesUsersType.PutType.class);
    final var search =
      this.transaction.queries(NPDatabaseQueriesUsersType.SearchType.class);

    final var users = generateUsers();
    for (final var u : users) {
      put.execute(u);
    }

    this.transaction.commit();

    final var params =
      new NPUserSearchParameters(
        new NPComparisonFuzzyType.IsSimilarTo<>("user3"),
        new NPComparisonSetType.Anything<>(),
        1000L
      );

    final var paged = search.execute(params);
    final var page = paged.pageCurrent(this.transaction);
    assertEquals(
      users.stream()
        .filter(u -> "user3".equals(u.name().value()))
        .collect(Collectors.toUnmodifiableSet()),
      Set.copyOf(page.items())
    );
  }

  /**
   * Searching for users works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testUserSearch2()
    throws Exception
  {
    final var put =
      this.transaction.queries(NPDatabaseQueriesUsersType.PutType.class);
    final var search =
      this.transaction.queries(NPDatabaseQueriesUsersType.SearchType.class);

    final var users = generateUsers();
    for (final var u : users) {
      put.execute(u);
    }

    this.transaction.commit();

    final var roleSet = Set.of(
      MRoleName.of("top10"),
      MRoleName.of("top20"),
      MRoleName.of("top50"),
      MRoleName.of("top80"),
      MRoleName.of("top90"),
      MRoleName.of("odd")
    );

    final var params =
      new NPUserSearchParameters(
        new NPComparisonFuzzyType.Anything<>(),
        new NPComparisonSetType.IsSubsetOf<>(roleSet),
        1000L
      );

    final var paged =
      search.execute(params);
    final var page =
      paged.pageCurrent(this.transaction);

    checkSameSets(users, page.items());
  }

  private static void checkSameSets(
    final List<NPUser> expected,
    final List<NPUser> received)
  {
    final var assertions = new ArrayList<Executable>();
    for (final var user : expected) {
      assertions.add(() -> {
        assertTrue(
          received.contains(user),
          "Received set contains %s".formatted(user)
        );
      });
    }
    assertAll(assertions);
  }

  /**
   * Searching for users works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testUserSearch3()
    throws Exception
  {
    final var put =
      this.transaction.queries(NPDatabaseQueriesUsersType.PutType.class);
    final var search =
      this.transaction.queries(NPDatabaseQueriesUsersType.SearchType.class);

    final var users = generateUsers();
    for (final var u : users) {
      put.execute(u);
    }

    this.transaction.commit();

    final var roleSet = Set.of(
      MRoleName.of("odd")
    );

    final var params =
      new NPUserSearchParameters(
        new NPComparisonFuzzyType.Anything<>(),
        new NPComparisonSetType.IsOverlapping<>(roleSet),
        1000L
      );

    final var paged =
      search.execute(params);
    final var page =
      paged.pageCurrent(this.transaction);

    assertEquals(
      users.stream()
        .filter(u -> u.subject().roles().contains(MRoleName.of("odd")))
        .collect(Collectors.toUnmodifiableSet()),
      Set.copyOf(page.items())
    );
  }

  /**
   * Searching for users works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testUserSearch4()
    throws Exception
  {
    final var put =
      this.transaction.queries(NPDatabaseQueriesUsersType.PutType.class);
    final var search =
      this.transaction.queries(NPDatabaseQueriesUsersType.SearchType.class);

    final var users = generateUsers();
    for (final var u : users) {
      put.execute(u);
    }

    this.transaction.commit();

    final var roleSet = Set.of(
      MRoleName.of("odd"),
      MRoleName.of("top50")
    );

    final var params =
      new NPUserSearchParameters(
        new NPComparisonFuzzyType.Anything<>(),
        new NPComparisonSetType.IsSupersetOf<>(roleSet),
        1000L
      );

    final var paged =
      search.execute(params);
    final var page =
      paged.pageCurrent(this.transaction);

    assertEquals(
      users.stream()
        .filter(u -> {
          final var roles = u.subject().roles();
          return roles.contains(MRoleName.of("odd"))
                 && roles.contains(MRoleName.of("top50"));
        })
        .collect(Collectors.toUnmodifiableSet()),
      Set.copyOf(page.items())
    );
  }

  /**
   * Searching for users works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testUserSearch5()
    throws Exception
  {
    final var put =
      this.transaction.queries(NPDatabaseQueriesUsersType.PutType.class);
    final var search =
      this.transaction.queries(NPDatabaseQueriesUsersType.SearchType.class);

    final var users = generateUsers();
    for (final var u : users) {
      put.execute(u);
    }

    this.transaction.commit();

    final var roleSet = Set.of(
      MRoleName.of("top50"),
      MRoleName.of("top80"),
      MRoleName.of("top90")
    );

    final var params =
      new NPUserSearchParameters(
        new NPComparisonFuzzyType.Anything<>(),
        new NPComparisonSetType.IsEqualTo<>(roleSet),
        1000L
      );

    final var paged =
      search.execute(params);
    final var page =
      paged.pageCurrent(this.transaction);

    assertEquals(
      users.stream()
        .filter(u -> u.subject().roles().equals(roleSet))
        .collect(Collectors.toUnmodifiableSet()),
      Set.copyOf(page.items())
    );
  }

  /**
   * Searching for users works.
   *
   * @throws Exception On errors
   */

  @Test
  public void testUserSearch6()
    throws Exception
  {
    final var put =
      this.transaction.queries(NPDatabaseQueriesUsersType.PutType.class);
    final var search =
      this.transaction.queries(NPDatabaseQueriesUsersType.SearchType.class);

    final var users = generateUsers();
    for (final var u : users) {
      put.execute(u);
    }

    this.transaction.commit();

    final var roleSet = Set.of(
      MRoleName.of("top90")
    );

    final var params =
      new NPUserSearchParameters(
        new NPComparisonFuzzyType.Anything<>(),
        new NPComparisonSetType.IsNotEqualTo<>(roleSet),
        1000L
      );

    final var paged =
      search.execute(params);
    final var page =
      paged.pageCurrent(this.transaction);

    final var expected =
      users.stream()
        .filter(u -> !u.subject().roles().equals(roleSet))
        .collect(Collectors.toList());

    checkSameSets(expected, page.items());
  }

  private static List<NPUser> generateUsers()
  {
    final var users = new ArrayList<NPUser>();
    for (int index = 0; index < 100; ++index) {
      final var roles = new HashSet<MRoleName>();
      if (index >= 10) {
        roles.add(new MRoleName(new RDottedName("top90")));
      }
      if (index >= 20) {
        roles.add(new MRoleName(new RDottedName("top80")));
      }
      if (index >= 50) {
        roles.add(new MRoleName(new RDottedName("top50")));
      }
      if (index >= 80) {
        roles.add(new MRoleName(new RDottedName("top20")));
      }
      if (index >= 90) {
        roles.add(new MRoleName(new RDottedName("top10")));
      }
      if (index % 2 != 0) {
        roles.add(new MRoleName(new RDottedName("odd")));
      }

      users.add(
        new NPUser(
          UUID.randomUUID(),
          new IdName("user%d".formatted(Integer.valueOf(index))),
          new MSubject(Set.copyOf(roles))
        )
      );
    }
    return List.copyOf(users);
  }
}
