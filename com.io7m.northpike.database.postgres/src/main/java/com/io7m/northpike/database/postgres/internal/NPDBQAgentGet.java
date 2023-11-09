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

package com.io7m.northpike.database.postgres.internal;

import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType.GetType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.agents.NPAgentDescription;
import com.io7m.northpike.model.agents.NPAgentID;
import com.io7m.northpike.model.agents.NPAgentKeyPairEd448Type;
import com.io7m.northpike.model.agents.NPAgentKeyPairFactoryEd448;
import com.io7m.northpike.model.agents.NPAgentKeyPublicType;
import com.io7m.northpike.model.agents.NPAgentLabel;
import com.io7m.northpike.model.agents.NPAgentLabelName;
import org.jooq.DSLContext;
import org.jooq.DataType;
import org.jooq.Field;
import org.jooq.impl.DSL;
import org.jooq.impl.SQLDataType;
import org.jooq.postgres.extensions.bindings.HstoreBinding;
import org.jooq.postgres.extensions.types.Hstore;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import static com.io7m.northpike.database.postgres.internal.Tables.AGENT_LABELS;
import static com.io7m.northpike.database.postgres.internal.Tables.AGENT_LABEL_DEFINITIONS;
import static com.io7m.northpike.database.postgres.internal.tables.Agents.AGENTS;

/**
 * Retrieve an agent.
 */

public final class NPDBQAgentGet
  extends NPDBQAbstract<NPAgentID, Optional<NPAgentDescription>>
  implements GetType
{
  private static final Service<NPAgentID, Optional<NPAgentDescription>, GetType> SERVICE =
    new Service<>(GetType.class, NPDBQAgentGet::new);

  private static final DataType<Hstore> A_DATA_TYPE =
    SQLDataType.OTHER.asConvertedDataType(new HstoreBinding());

  static final Field<Hstore> A_ENVIRONMENT =
    DSL.field("A_ENVIRONMENT", A_DATA_TYPE);

  static final Field<Hstore> A_PROPERTIES =
    DSL.field("A_PROPERTIES", A_DATA_TYPE);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQAgentGet(
    final NPDatabaseTransaction transaction)
  {
    super(transaction);
  }

  /**
   * @return A query provider
   */

  public static NPDBQueryProviderType provider()
  {
    return () -> SERVICE;
  }

  @Override
  protected Optional<NPAgentDescription> onExecute(
    final DSLContext context,
    final NPAgentID id)
    throws NPDatabaseException
  {
    final var query =
      context.select(
          AGENTS.A_ID,
          AGENTS.A_NAME,
          A_ENVIRONMENT,
          A_PROPERTIES,
          AGENTS.A_PUBLIC_KEY_DATA,
          AGENTS.A_PUBLIC_KEY_ALGO,
          AGENT_LABEL_DEFINITIONS.ALD_NAME,
          AGENT_LABEL_DEFINITIONS.ALD_DESCRIPTION
        ).from(AGENTS)
        .leftOuterJoin(AGENT_LABELS)
        .on(AGENTS.A_ID.eq(AGENT_LABELS.AL_AGENT))
        .leftOuterJoin(AGENT_LABEL_DEFINITIONS)
        .on(AGENT_LABEL_DEFINITIONS.ALD_ID.eq(AGENT_LABELS.AL_LABEL))
        .where(
          AGENTS.A_ID.eq(id.value())
            .and(AGENTS.A_DELETED.eq(Boolean.FALSE))
        );

    recordQuery(query);
    final var result = query.fetch();
    if (result.isEmpty()) {
      return Optional.empty();
    }

    String name = null;
    NPAgentKeyPublicType key = null;

    final var environment =
      new HashMap<String, String>();
    final var properties =
      new HashMap<String, String>();
    final var labels =
      new HashMap<NPAgentLabelName, NPAgentLabel>();

    boolean first = true;
    for (final var record : result) {
      if (first) {
        name = record.get(AGENTS.A_NAME);
        key = parseKey(record);
        first = false;
      }

      environment.putAll(
        record.get(A_ENVIRONMENT).data());
      properties.putAll(
        record.get(A_PROPERTIES).data());
      final var lName =
        record.get(AGENT_LABEL_DEFINITIONS.ALD_NAME);
      final var lDesc =
        record.get(AGENT_LABEL_DEFINITIONS.ALD_DESCRIPTION);

      if (lName != null) {
        final var label = new NPAgentLabel(NPAgentLabelName.of(lName), lDesc);
        labels.put(label.name(), label);
      }
    }

    return Optional.of(
      new NPAgentDescription(
        id,
        name,
        key,
        Map.copyOf(environment),
        Map.copyOf(properties),
        Map.copyOf(labels)
      )
    );
  }

  private static final NPAgentKeyPairFactoryEd448 ED_448 =
    new NPAgentKeyPairFactoryEd448();

  private static NPAgentKeyPublicType parseKey(
    final org.jooq.Record r)
    throws NPDatabaseException
  {
    try {
      final var algorithm =
        r.get(AGENTS.A_PUBLIC_KEY_ALGO);

      return switch (algorithm) {
        case NPAgentKeyPairEd448Type.ALGORITHM_NAME -> {
          yield ED_448.parsePublicKeyFromText(r.get(AGENTS.A_PUBLIC_KEY_DATA));
        }
        default -> {
          throw new IllegalStateException(
            "Unrecognized key algorithm: %s".formatted(algorithm)
          );
        }
      };
    } catch (final NPException e) {
      throw new NPDatabaseException(
        e.getMessage(),
        e,
        e.errorCode(),
        e.attributes(),
        e.remediatingAction()
      );
    }
  }
}
