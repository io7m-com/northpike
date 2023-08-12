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

import com.io7m.northpike.database.api.NPDatabaseFactoryType;
import com.io7m.northpike.database.postgres.NPPGDatabases;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType;

/**
 * Continuous integration (PostgreSQL Database)
 */

module com.io7m.northpike.database.postgres
{
  requires static org.osgi.annotation.bundle;
  requires static org.osgi.annotation.versioning;

  requires com.io7m.northpike.database.api;
  requires com.io7m.northpike.model;
  requires com.io7m.northpike.strings;

  requires com.io7m.jqpage.core;
  requires com.io7m.anethum.api;
  requires com.io7m.jaffirm.core;
  requires com.io7m.jmulticlose.core;
  requires com.io7m.trasco.api;
  requires com.io7m.trasco.vanilla;
  requires com.zaxxer.hikari;
  requires io.opentelemetry.api;
  requires io.opentelemetry.context;
  requires io.opentelemetry.semconv;
  requires java.sql;
  requires org.jgrapht.core;
  requires org.jooq;
  requires org.postgresql.jdbc;
  requires org.slf4j;

  provides NPDatabaseFactoryType
    with NPPGDatabases;

  uses NPDBQueryProviderType;

  provides NPDBQueryProviderType with
com.io7m.northpike.database.postgres.internal.NPDBQAgentGet,
com.io7m.northpike.database.postgres.internal.NPDBQAgentLabelGet,
com.io7m.northpike.database.postgres.internal.NPDBQAgentLabelPut,
com.io7m.northpike.database.postgres.internal.NPDBQAgentList,
com.io7m.northpike.database.postgres.internal.NPDBQAgentPut,
com.io7m.northpike.database.postgres.internal.NPDBQMaintenance,
com.io7m.northpike.database.postgres.internal.NPDBQRepositoryCommitsGet,
com.io7m.northpike.database.postgres.internal.NPDBQRepositoryCommitsPut,
com.io7m.northpike.database.postgres.internal.NPDBQRepositoryGet,
com.io7m.northpike.database.postgres.internal.NPDBQRepositoryPut,
com.io7m.northpike.database.postgres.internal.NPDBQSCMProviderGet,
com.io7m.northpike.database.postgres.internal.NPDBQSCMProviderPut,
com.io7m.northpike.database.postgres.internal.NPDBQUserGet,
com.io7m.northpike.database.postgres.internal.NPDBQUserPut,
com.io7m.northpike.database.postgres.internal.NPDBQToolExecutionDescriptionGet,
com.io7m.northpike.database.postgres.internal.NPDBQToolExecutionDescriptionPut
    ;

  exports com.io7m.northpike.database.postgres;
}
