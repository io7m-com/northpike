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


package com.io7m.northpike.shell.commons;

import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.preferences.api.NPPreferencesServiceType;
import com.io7m.northpike.strings.NPStringConstantType;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QParameterType;
import com.io7m.repetoir.core.RPServiceDirectoryType;
import org.jline.reader.Completer;
import org.jline.reader.impl.completer.StringsCompleter;
import org.jline.terminal.Terminal;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;

/**
 * The abstract base class for shell commands.
 */

public abstract class NPShellCmdAbstract
  implements NPShellCmdType
{
  private final HashMap<String, String> attributes;
  private final RPServiceDirectoryType services;
  private final QCommandMetadata metadata;

  protected NPShellCmdAbstract(
    final RPServiceDirectoryType inServices,
    final QCommandMetadata inMetadata)
  {
    this.services =
      Objects.requireNonNull(inServices, "services");
    this.metadata =
      Objects.requireNonNull(inMetadata, "metadata");
    this.attributes =
      new HashMap<String, String>();
  }

  @Override
  public final void reset()
  {
    this.attributes.clear();
  }

  @Override
  public final QCommandMetadata metadata()
  {
    return this.metadata;
  }

  protected final Terminal terminal()
  {
    return this.services()
      .requireService(NPShellTerminalHolder.class)
      .terminal();
  }

  protected final NPShellOptions options()
  {
    return this.services().requireService(NPShellOptions.class);
  }

  protected final RPServiceDirectoryType services()
  {
    return this.services;
  }

  protected final NPFormatterType formatter()
  {
    return this.options().formatter();
  }

  protected final void setAttribute(
    final NPStringConstantType name,
    final Object value)
  {
    this.attributes.put(
      this.services.requireService(NPStrings.class).format(name),
      value.toString()
    );
  }

  protected final NPException fail(
    final NPErrorCode errorCode,
    final NPStringConstantType message)
  {
    return new NPException(
      this.services.requireService(NPStrings.class)
        .format(message),
      errorCode,
      Map.copyOf(this.attributes),
      Optional.empty()
    );
  }

  protected final NPPreferencesServiceType preferences()
  {
    return this.services()
      .requireService(NPPreferencesServiceType.class);
  }

  @Override
  public final String toString()
  {
    return "[%s]".formatted(this.getClass().getSimpleName());
  }

  @Override
  public final Completer completer()
  {
    return new StringsCompleter(
      this.onListNamedParameters()
        .stream()
        .map(QParameterType::name)
        .toList()
    );
  }
}
