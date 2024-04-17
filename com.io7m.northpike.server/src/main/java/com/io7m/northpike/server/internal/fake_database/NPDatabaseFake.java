/*
 * Copyright © 2024 Mark Raynsford <code@io7m.com> https://www.io7m.com
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


package com.io7m.northpike.server.internal.fake_database;

import com.io7m.northpike.database.api.NPDatabaseConnectionType;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesType;
import com.io7m.northpike.database.api.NPDatabaseRole;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.model.NPAuditOwnerType;

/**
 * A fake database.
 */

public final class NPDatabaseFake implements NPDatabaseType
{
  /**
   * A fake database.
   */

  public NPDatabaseFake()
  {

  }

  @Override
  public void close()
    throws NPDatabaseException
  {

  }

  @Override
  public NPDatabaseConnectionType openConnection(
    final NPDatabaseRole role)
    throws NPDatabaseException
  {
    return new NPDatabaseFakeConnection();
  }

  @Override
  public NPDatabaseTransactionType transaction(
    final NPDatabaseRole role)
    throws NPDatabaseException
  {
    return new NPDatabaseFakeConnection()
      .openTransaction();
  }

  @Override
  public String description()
  {
    return "A fake database.";
  }

  private static final class NPDatabaseFakeTransaction
    implements NPDatabaseTransactionType
  {
    NPDatabaseFakeTransaction()
    {

    }

    @Override
    public void close()
    {

    }

    @Override
    public <T extends NPDatabaseQueriesType> T queries(
      final Class<T> queryClass)
    {
      throw new UnsupportedOperationException();
    }

    @Override
    public void rollback()
    {

    }

    @Override
    public void commit()
    {

    }

    @Override
    public void setOwner(
      final NPAuditOwnerType newOwner)
    {

    }

    @Override
    public NPAuditOwnerType owner()
    {
      return new NPAuditOwnerType.Server();
    }
  }

  private static final class NPDatabaseFakeConnection
    implements NPDatabaseConnectionType
  {
    NPDatabaseFakeConnection()
    {

    }

    @Override
    public void close()
    {

    }

    @Override
    public NPDatabaseTransactionType openTransaction()
    {
      return new NPDatabaseFakeTransaction();
    }
  }
}
