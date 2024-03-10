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


package com.io7m.northpike.shell.main;

import com.io7m.jade.api.ApplicationDirectories;
import com.io7m.jade.api.ApplicationDirectoryConfiguration;
import com.io7m.northpike.shell.NPShellConfiguration;
import com.io7m.northpike.shell.NPShells;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.user_client.NPUserClients;
import org.slf4j.bridge.SLF4JBridgeHandler;

import java.util.Locale;
import java.util.Optional;

/**
 * The main shell entry point.
 */

public final class NPShellMain
{
  private NPShellMain()
  {

  }

  /**
   * The main shell entry point.
   *
   * @param args The command-line arguments
   *
   * @throws Exception On errors
   */

  public static void main(
    final String[] args)
    throws Exception
  {
    System.exit(run(args));
  }

  /**
   * The main shell entry point.
   *
   * @param args The command-line arguments
   *
   * @return The shell exit code
   *
   * @throws Exception On errors
   */

  public static int run(
    final String[] args)
    throws Exception
  {
    System.setProperty("org.jooq.no-tips", "true");
    System.setProperty("org.jooq.no-logo", "true");

    SLF4JBridgeHandler.removeHandlersForRootLogger();
    SLF4JBridgeHandler.install();

    final var directoryConfiguration =
      ApplicationDirectoryConfiguration.builder()
        .setApplicationName("com.io7m.northpike.shell")
        .setOverridePropertyName("com.io7m.northpike.override")
        .setPortablePropertyName("com.io7m.northpike.portable")
        .build();

    final var applicationConfiguration =
      ApplicationDirectories.get(directoryConfiguration);

    final var configuration =
      new NPShellConfiguration(
        Locale.getDefault(),
        applicationConfiguration.configurationDirectory(),
        new NPUserClients(),
        NPStrings.create(Locale.getDefault()),
        Optional.empty(),
        1_000_000
      );

    final var shells = new NPShells();
    try (var shell = shells.create(configuration)) {
      shell.run();
      return shell.exitCode();
    }
  }
}
