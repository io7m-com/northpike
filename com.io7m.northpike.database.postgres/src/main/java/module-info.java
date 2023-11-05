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
  requires com.io7m.northpike.plans.parsers;
  requires com.io7m.northpike.strings;

  requires com.io7m.anethum.api;
  requires com.io7m.cedarbridge.runtime.api;
  requires com.io7m.cedarbridge.runtime.bssio;
  requires com.io7m.cedarbridge.runtime.convenience;
  requires com.io7m.jaffirm.core;
  requires com.io7m.jbssio.api;
  requires com.io7m.jbssio.vanilla;
  requires com.io7m.jmulticlose.core;
  requires com.io7m.jqpage.core;
  requires com.io7m.trasco.api;
  requires com.io7m.trasco.vanilla;
  requires com.zaxxer.hikari;
  requires io.opentelemetry.api;
  requires io.opentelemetry.context;
  requires io.opentelemetry.semconv;
  requires java.sql;
  requires org.jgrapht.core;
  requires org.jooq.postgres.extensions;
  requires org.jooq;
  requires org.postgresql.jdbc;
  requires org.slf4j;

  provides NPDatabaseFactoryType
    with NPPGDatabases;

  uses NPDBQueryProviderType;

  provides NPDBQueryProviderType with
    com.io7m.northpike.database.postgres.internal.NPDBQAgentDelete,
    com.io7m.northpike.database.postgres.internal.NPDBQAgentGet,
    com.io7m.northpike.database.postgres.internal.NPDBQAgentGetByKey,
    com.io7m.northpike.database.postgres.internal.NPDBQAgentLabelDelete,
    com.io7m.northpike.database.postgres.internal.NPDBQAgentLabelGet,
    com.io7m.northpike.database.postgres.internal.NPDBQAgentLabelPut,
    com.io7m.northpike.database.postgres.internal.NPDBQAgentLabelSearch,
    com.io7m.northpike.database.postgres.internal.NPDBQAgentLoginChallengeDelete,
    com.io7m.northpike.database.postgres.internal.NPDBQAgentLoginChallengeGet,
    com.io7m.northpike.database.postgres.internal.NPDBQAgentLoginChallengePut,
    com.io7m.northpike.database.postgres.internal.NPDBQAgentLoginChallengeSearch,
    com.io7m.northpike.database.postgres.internal.NPDBQAgentPut,
    com.io7m.northpike.database.postgres.internal.NPDBQAgentSearch,
    com.io7m.northpike.database.postgres.internal.NPDBQArchiveGet,
    com.io7m.northpike.database.postgres.internal.NPDBQArchivePut,
    com.io7m.northpike.database.postgres.internal.NPDBQAssignmentCommitsNotExecuted,
    com.io7m.northpike.database.postgres.internal.NPDBQAssignmentExecutionDelete,
    com.io7m.northpike.database.postgres.internal.NPDBQAssignmentExecutionGet,
    com.io7m.northpike.database.postgres.internal.NPDBQAssignmentExecutionLogAdd,
    com.io7m.northpike.database.postgres.internal.NPDBQAssignmentExecutionLogList,
    com.io7m.northpike.database.postgres.internal.NPDBQAssignmentExecutionPut,
    com.io7m.northpike.database.postgres.internal.NPDBQAssignmentExecutionWorkItems,
    com.io7m.northpike.database.postgres.internal.NPDBQAssignmentExecutionsCancelAll,
    com.io7m.northpike.database.postgres.internal.NPDBQAssignmentExecutionsSearch,
    com.io7m.northpike.database.postgres.internal.NPDBQAssignmentGet,
    com.io7m.northpike.database.postgres.internal.NPDBQAssignmentPut,
    com.io7m.northpike.database.postgres.internal.NPDBQAssignmentSearch,
    com.io7m.northpike.database.postgres.internal.NPDBQAuditEventAdd,
    com.io7m.northpike.database.postgres.internal.NPDBQAuditEventSearch,
    com.io7m.northpike.database.postgres.internal.NPDBQMaintenanceDeleteExpiredArchives,
    com.io7m.northpike.database.postgres.internal.NPDBQMaintenanceDeleteExpiredAssignmentExecutions,
    com.io7m.northpike.database.postgres.internal.NPDBQMaintenanceDeleteExpiredAudit,
    com.io7m.northpike.database.postgres.internal.NPDBQMaintenanceDeleteExpiredLoginChallenges,
    com.io7m.northpike.database.postgres.internal.NPDBQMaintenanceUpdateUserRoles,
    com.io7m.northpike.database.postgres.internal.NPDBQPlanDelete,
    com.io7m.northpike.database.postgres.internal.NPDBQPlanGet,
    com.io7m.northpike.database.postgres.internal.NPDBQPlanGetRaw,
    com.io7m.northpike.database.postgres.internal.NPDBQPlanPut,
    com.io7m.northpike.database.postgres.internal.NPDBQPlanSearch,
    com.io7m.northpike.database.postgres.internal.NPDBQPublicKeyDelete,
    com.io7m.northpike.database.postgres.internal.NPDBQPublicKeyGet,
    com.io7m.northpike.database.postgres.internal.NPDBQPublicKeyPut,
    com.io7m.northpike.database.postgres.internal.NPDBQPublicKeySearch,
    com.io7m.northpike.database.postgres.internal.NPDBQRepositoryCommitGet,
    com.io7m.northpike.database.postgres.internal.NPDBQRepositoryCommitsGet,
    com.io7m.northpike.database.postgres.internal.NPDBQRepositoryCommitsGetMostRecentlyReceived,
    com.io7m.northpike.database.postgres.internal.NPDBQRepositoryCommitsPut,
    com.io7m.northpike.database.postgres.internal.NPDBQRepositoryGet,
    com.io7m.northpike.database.postgres.internal.NPDBQRepositoryList,
    com.io7m.northpike.database.postgres.internal.NPDBQRepositoryPublicKeyAssign,
    com.io7m.northpike.database.postgres.internal.NPDBQRepositoryPublicKeyIsAssigned,
    com.io7m.northpike.database.postgres.internal.NPDBQRepositoryPublicKeyUnassign,
    com.io7m.northpike.database.postgres.internal.NPDBQRepositoryPublicKeysAssigned,
    com.io7m.northpike.database.postgres.internal.NPDBQRepositoryPut,
    com.io7m.northpike.database.postgres.internal.NPDBQSCMProviderGet,
    com.io7m.northpike.database.postgres.internal.NPDBQSCMProviderPut,
    com.io7m.northpike.database.postgres.internal.NPDBQToolExecutionDescriptionDelete,
    com.io7m.northpike.database.postgres.internal.NPDBQToolExecutionDescriptionGet,
    com.io7m.northpike.database.postgres.internal.NPDBQToolExecutionDescriptionPut,
    com.io7m.northpike.database.postgres.internal.NPDBQToolExecutionDescriptionSearch,
    com.io7m.northpike.database.postgres.internal.NPDBQUserGet,
    com.io7m.northpike.database.postgres.internal.NPDBQUserPut,
    com.io7m.northpike.database.postgres.internal.NPDBQUserSearch,
    com.io7m.northpike.database.postgres.internal.NPDBQWorkItemGet,
    com.io7m.northpike.database.postgres.internal.NPDBQWorkItemLogAdd,
    com.io7m.northpike.database.postgres.internal.NPDBQWorkItemPut
    ;

  exports com.io7m.northpike.database.postgres;
}
