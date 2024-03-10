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

package com.io7m.northpike.tests;


import com.io7m.northpike.model.tls.NPTLSDisabled;
import com.io7m.northpike.model.tls.NPTLSEnabledExplicit;
import com.io7m.northpike.model.tls.NPTLSStoreConfiguration;
import com.io7m.northpike.preferences.api.NPPreferenceServerBookmark;
import com.io7m.northpike.preferences.api.NPPreferenceServerUsernamePassword;
import com.io7m.northpike.preferences.api.NPPreferences;
import com.io7m.northpike.preferences.api.NPPreferencesDebuggingEnabled;
import com.io7m.northpike.preferences.basic.NPPreferencesService;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.IOException;
import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

public final class NPPreferencesTest
{
  private Path directory;

  @BeforeEach
  public void setup(
    final @TempDir Path directory)
    throws Exception
  {
    this.directory = directory;
  }

  @Test
  public void testPreferencesLoadStoreIdentity()
    throws IOException
  {
    final var service =
      NPPreferencesService.openOrDefault(
        this.directory.resolve("prefs.txt"));

    final var prefsInitial = service.preferences();
    service.save(prefsInitial);
    assertEquals(prefsInitial, service.preferences());
  }

  @Test
  public void testPreferencesLoadStoreChanged()
    throws IOException
  {
    final var service =
      NPPreferencesService.openOrDefault(
        this.directory.resolve("prefs.txt"));

    final var prefsNew =
      new NPPreferences(
        NPPreferencesDebuggingEnabled.DEBUGGING_ENABLED,
        List.of(
          new NPPreferenceServerBookmark(
            "name1", "host", 1000, NPTLSDisabled.TLS_DISABLED,
            new NPPreferenceServerUsernamePassword("user", "pass")
          ),
          new NPPreferenceServerBookmark(
            "name2", "host", 1000, new NPTLSEnabledExplicit(
            new NPTLSStoreConfiguration("JKS", "SUNW", "1234", this.directory),
            new NPTLSStoreConfiguration("JKS", "SUNW", "1234", this.directory)
          ),
            new NPPreferenceServerUsernamePassword("user", "pass")
          ),
          new NPPreferenceServerBookmark(
            "name3", "host", 1000, NPTLSDisabled.TLS_DISABLED,
            new NPPreferenceServerUsernamePassword("user", "pass")
          )
        ),
        List.of(
          this.directory,
          this.directory.resolve("a"),
          this.directory.resolve("b")
        )
      );

    service.save(prefsNew);
    assertEquals(prefsNew, service.preferences());
  }

  @Test
  public void testPreferencesLoadStoreUpdate()
    throws IOException
  {
    final var service0 =
      NPPreferencesService.openOrDefault(
        this.directory.resolve("prefs.txt"));

    final var p =
      new NPPreferences(
        NPPreferencesDebuggingEnabled.DEBUGGING_ENABLED,
        List.of(
          new NPPreferenceServerBookmark(
            "name1", "host", 1000, NPTLSDisabled.TLS_DISABLED,
            new NPPreferenceServerUsernamePassword("user", "pass")
          ),
          new NPPreferenceServerBookmark(
            "name2", "host", 1000, new NPTLSEnabledExplicit(
            new NPTLSStoreConfiguration("JKS", "SUNW", "1234", this.directory),
            new NPTLSStoreConfiguration("JKS", "SUNW", "1234", this.directory)
          ),
            new NPPreferenceServerUsernamePassword("user", "pass")
          ),
          new NPPreferenceServerBookmark(
            "name3", "host", 1000, NPTLSDisabled.TLS_DISABLED,
            new NPPreferenceServerUsernamePassword("user", "pass")
          )
        ),
        List.of(
          this.directory,
          this.directory.resolve("a"),
          this.directory.resolve("b")
        )
      );
    service0.update(q -> p);
    assertEquals(p, service0.preferences());

    final var service1 =
      NPPreferencesService.openOrDefault(
        this.directory.resolve("prefs.txt"));

    assertEquals(p, service1.preferences());
  }
}
