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


package com.io7m.northpike.server.configuration.v1;

import com.io7m.blackthorne.core.BTElementHandlerType;
import com.io7m.blackthorne.core.BTElementParsingContextType;
import com.io7m.northpike.server.configuration.NPSCDatabase;
import com.io7m.northpike.server.configuration.NPSCDatabaseKind;
import org.xml.sax.Attributes;

import java.util.Optional;

/**
 * A parser for {@link NPSCDatabase}
 */

public final class NPSC1Database
  implements BTElementHandlerType<Object, NPSCDatabase>
{
  private NPSCDatabaseKind kind;
  private String ownerRoleName;
  private String ownerRolePassword;
  private String workerRolePassword;
  private Optional<String> readerRolePassword;
  private String address;
  private int port;
  private String databaseName;
  private String databaseLanguage;
  private boolean create;
  private boolean upgrade;
  private boolean useTLS;

  /**
   * A parser for {@link NPSCDatabase}
   *
   * @param context The parse context
   */

  public NPSC1Database(
    final BTElementParsingContextType context)
  {

  }

  @Override
  public void onElementStart(
    final BTElementParsingContextType context,
    final Attributes attributes)
  {
    this.kind =
      NPSCDatabaseKind.valueOf(attributes.getValue("Kind"));
    this.ownerRoleName =
      attributes.getValue("OwnerRoleName");
    this.ownerRolePassword =
      attributes.getValue("OwnerRolePassword");
    this.workerRolePassword =
      attributes.getValue("WorkerRolePassword");
    this.readerRolePassword =
      Optional.ofNullable(attributes.getValue("ReaderRolePassword"));
    this.address =
      attributes.getValue("Address");
    this.port =
      Integer.parseUnsignedInt(attributes.getValue("Port"));
    this.databaseName =
      attributes.getValue("Name");
    this.databaseLanguage =
      attributes.getValue("Language");
    this.create =
      Boolean.parseBoolean(attributes.getValue("Create"));
    this.upgrade =
      Boolean.parseBoolean(attributes.getValue("Upgrade"));
    this.useTLS =
      Boolean.parseBoolean(attributes.getValue("UseTLS"));
  }

  @Override
  public NPSCDatabase onElementFinished(
    final BTElementParsingContextType context)
  {
    return new NPSCDatabase(
      this.kind,
      this.ownerRoleName,
      this.ownerRolePassword,
      this.workerRolePassword,
      this.readerRolePassword,
      this.address,
      this.port,
      this.databaseName,
      this.databaseLanguage,
      this.create,
      this.upgrade,
      this.useTLS
    );
  }
}
