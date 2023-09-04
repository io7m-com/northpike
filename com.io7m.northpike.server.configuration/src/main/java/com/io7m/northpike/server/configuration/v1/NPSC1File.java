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

import com.io7m.blackthorne.core.BTElementHandlerConstructorType;
import com.io7m.blackthorne.core.BTElementHandlerType;
import com.io7m.blackthorne.core.BTElementParsingContextType;
import com.io7m.blackthorne.core.BTQualifiedName;
import com.io7m.northpike.server.api.NPServerAgentConfiguration;
import com.io7m.northpike.server.api.NPServerArchiveConfiguration;
import com.io7m.northpike.server.api.NPServerDirectoryConfiguration;
import com.io7m.northpike.server.api.NPServerIdstoreConfiguration;
import com.io7m.northpike.server.api.NPServerUserConfiguration;
import com.io7m.northpike.server.configuration.NPSCDatabase;
import com.io7m.northpike.server.configuration.NPSCFile;
import com.io7m.northpike.telemetry.api.NPTelemetryConfiguration;

import java.util.Map;
import java.util.Optional;

import static com.io7m.northpike.server.configuration.v1.NPSCv1.element;
import static java.util.Map.entry;

/**
 * A parser for {@link NPSCFile}
 */

public final class NPSC1File
  implements BTElementHandlerType<Object, NPSCFile>
{
  private NPServerAgentConfiguration agent;
  private NPServerIdstoreConfiguration idstore;
  private NPTelemetryConfiguration telemetry;
  private NPSCDatabase database;
  private NPServerDirectoryConfiguration directories;
  private NPServerArchiveConfiguration archive;
  private NPServerUserConfiguration user;

  /**
   * A parser for {@link NPSCFile}
   *
   * @param context The parse context
   */

  public NPSC1File(
    final BTElementParsingContextType context)
  {

  }

  @Override
  public Map<BTQualifiedName, BTElementHandlerConstructorType<?, ?>>
  onChildHandlersRequested(
    final BTElementParsingContextType context)
  {
    return Map.ofEntries(
      entry(element("AgentService"), NPSC1AgentService::new),
      entry(element("ArchiveService"), NPSC1ArchiveService::new),
      entry(element("Database"), NPSC1Database::new),
      entry(element("Directories"), NPSC1Directories::new),
      entry(element("IdStore"), NPSC1Idstore::new),
      entry(element("OpenTelemetry"), NPSC1OpenTelemetry::new),
      entry(element("UserService"), NPSC1UserService::new)
    );
  }

  @Override
  public void onChildValueProduced(
    final BTElementParsingContextType context,
    final Object result)
  {
    if (result instanceof final NPServerAgentConfiguration e) {
      this.agent = e;
      return;
    }
    if (result instanceof final NPServerUserConfiguration e) {
      this.user = e;
      return;
    }
    if (result instanceof final NPServerArchiveConfiguration e) {
      this.archive = e;
      return;
    }
    if (result instanceof final NPServerIdstoreConfiguration e) {
      this.idstore = e;
      return;
    }
    if (result instanceof final NPTelemetryConfiguration e) {
      this.telemetry = e;
      return;
    }
    if (result instanceof final NPServerDirectoryConfiguration e) {
      this.directories = e;
      return;
    }
    if (result instanceof final NPSCDatabase e) {
      this.database = e;
      return;
    }
  }

  @Override
  public NPSCFile onElementFinished(
    final BTElementParsingContextType context)
  {
    return new NPSCFile(
      this.database,
      this.directories,
      this.idstore,
      this.agent,
      this.archive,
      this.user,
      Optional.ofNullable(this.telemetry)
    );
  }
}
