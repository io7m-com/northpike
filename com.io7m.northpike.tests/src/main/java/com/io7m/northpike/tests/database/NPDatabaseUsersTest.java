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
import com.io7m.medrina.api.MRoleName;
import com.io7m.medrina.api.MSubject;
import com.io7m.northpike.database.api.NPDatabaseConnectionType;
import com.io7m.northpike.database.api.NPDatabaseQueriesMaintenanceType;
import com.io7m.northpike.database.api.NPDatabaseQueriesUsersType;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.database.api.NPDatabaseUnit;
import com.io7m.northpike.model.NPUser;
import com.io7m.northpike.model.security.NPSecRole;
import com.io7m.northpike.tests.containers.NPTestContainerInstances;
import com.io7m.northpike.tests.containers.NPTestContainers;
import com.io7m.zelador.test_extension.CloseableResourcesType;
import com.io7m.zelador.test_extension.ZeladorExtension;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;

import java.util.Optional;
import java.util.Set;
import java.util.UUID;
import java.util.stream.Collectors;

import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE;
import static com.io7m.northpike.model.security.NPSecRole.ADMINISTRATOR;
import static com.io7m.northpike.model.security.NPSecRole.allRoles;
import static org.junit.jupiter.api.Assertions.assertEquals;

@ExtendWith({ErvillaExtension.class, ZeladorExtension.class})
@ErvillaConfiguration(projectName = "com.io7m.northpike", disabledIfUnsupported = true)
public final class NPDatabaseUsersTest
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

    this.transaction.setUserId(user.userId());
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

    this.transaction.setUserId(user.userId());
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
  public void testUserAdminMaintenance()
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

    final var userWithAllRoles =
      new NPUser(
        user.userId(),
        user.name(),
        new MSubject(
          allRoles()
            .stream()
            .filter(r -> r != NPSecRole.LOGIN)
            .map(NPSecRole::role)
            .collect(Collectors.toUnmodifiableSet())
        )
      );

    this.transaction.setUserId(user.userId());
    put.execute(user);
    maintenance.execute(NPDatabaseUnit.UNIT);

    assertEquals(userWithAllRoles, get.execute(user.userId()).orElseThrow());
  }
}
