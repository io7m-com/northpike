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

package com.io7m.northpike.shell;

import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.user_client.api.NPUserClientFactoryType;
import org.jline.terminal.Terminal;

import java.nio.file.Path;
import java.util.Locale;
import java.util.Objects;
import java.util.Optional;

/**
 * The shell configuration.
 *
 * @param locale                 The locale
 * @param configurationDirectory The configuration directory
 * @param userClients            The user clients
 * @param terminal               The terminal
 * @param strings                The strings
 * @param messageSizeLimit       The message size limit
 */

public record NPShellConfiguration(
  Locale locale,
  Path configurationDirectory,
  NPUserClientFactoryType userClients,
  NPStrings strings,
  Optional<Terminal> terminal,
  int messageSizeLimit)
{
  /**
   * The shell configuration.
   *
   * @param locale                 The locale
   * @param configurationDirectory The configuration directory
   * @param userClients            The user clients
   * @param terminal               The terminal
   * @param strings                The strings
   * @param messageSizeLimit       The message size limit
   */

  public NPShellConfiguration
  {
    Objects.requireNonNull(locale, "locale");
    Objects.requireNonNull(configurationDirectory, "configurationDirectory");
    Objects.requireNonNull(userClients, "userClients");
    Objects.requireNonNull(terminal, "terminal");
    Objects.requireNonNull(strings, "strings");
  }
}
