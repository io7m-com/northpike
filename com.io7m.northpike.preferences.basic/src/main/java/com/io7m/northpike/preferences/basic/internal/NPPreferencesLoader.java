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

package com.io7m.northpike.preferences.basic.internal;


import com.io7m.jproperties.JPropertyIncorrectType;
import com.io7m.jproperties.JPropertyNonexistent;
import com.io7m.northpike.model.tls.NPTLSConfigurationKind;
import com.io7m.northpike.model.tls.NPTLSConfigurationType;
import com.io7m.northpike.model.tls.NPTLSDisabled;
import com.io7m.northpike.model.tls.NPTLSEnabledClientAnonymous;
import com.io7m.northpike.model.tls.NPTLSEnabledExplicit;
import com.io7m.northpike.model.tls.NPTLSStoreConfiguration;
import com.io7m.northpike.preferences.api.NPPreferenceServerBookmark;
import com.io7m.northpike.preferences.api.NPPreferenceServerCredentialsType;
import com.io7m.northpike.preferences.api.NPPreferenceServerUsernamePassword;
import com.io7m.northpike.preferences.api.NPPreferences;
import com.io7m.northpike.preferences.api.NPPreferencesDebuggingEnabled;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.nio.file.FileSystem;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.Properties;

import static com.io7m.jproperties.JProperties.getBooleanWithDefault;
import static com.io7m.jproperties.JProperties.getInteger;
import static com.io7m.jproperties.JProperties.getString;
import static com.io7m.northpike.preferences.api.NPPreferencesDebuggingEnabled.DEBUGGING_DISABLED;
import static com.io7m.northpike.preferences.api.NPPreferencesDebuggingEnabled.DEBUGGING_ENABLED;


/**
 * A preferences loader.
 */

public final class NPPreferencesLoader
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPPreferencesLoader.class);

  private final FileSystem fileSystem;
  private final Properties properties;

  /**
   * A preferences loader.
   *
   * @param inFileSystem The filesystem used for paths
   * @param inProperties Properties
   */

  public NPPreferencesLoader(
    final FileSystem inFileSystem,
    final Properties inProperties)
  {
    this.fileSystem =
      Objects.requireNonNull(inFileSystem, "fileSystem");
    this.properties =
      Objects.requireNonNull(inProperties, "properties");
  }

  /**
   * @return A loaded set of preferences
   */

  public NPPreferences load()
  {
    return new NPPreferences(
      this.loadDebuggingEnabled(),
      this.loadServerBookmarks(),
      this.loadRecentFiles()
    );
  }

  private List<Path> loadRecentFiles()
  {
    final var countText = this.properties.getProperty("recentFiles.count");
    if (countText == null) {
      return List.of();
    }

    int count = 0;
    try {
      count = Integer.parseUnsignedInt(countText);
    } catch (final NumberFormatException e) {
      LOG.error("unable to load recent files: ", e);
    }

    final var results = new ArrayList<Path>();
    for (int index = 0; index < count; ++index) {
      try {
        results.add(this.loadRecentFile(Integer.valueOf(index)));
      } catch (final Exception e) {
        LOG.error("failed to load recent file: ", e);
      }
    }

    LOG.debug("loaded {} recent files", Integer.valueOf(results.size()));
    return List.copyOf(results);
  }

  private Path loadRecentFile(
    final Integer index)
    throws JPropertyNonexistent
  {
    return this.fileSystem.getPath(
      getString(this.properties, String.format("recentFiles.%s", index))
    );
  }

  private NPPreferencesDebuggingEnabled loadDebuggingEnabled()
  {
    try {
      if (getBooleanWithDefault(this.properties, "debugging", false)) {
        return DEBUGGING_ENABLED;
      }
      return DEBUGGING_DISABLED;
    } catch (final JPropertyIncorrectType e) {
      return DEBUGGING_DISABLED;
    }
  }

  private List<NPPreferenceServerBookmark> loadServerBookmarks()
  {
    final var countText = this.properties.getProperty("server.bookmarks");
    if (countText == null) {
      return List.of();
    }

    int count = 0;
    try {
      count = Integer.parseUnsignedInt(countText);
    } catch (final NumberFormatException e) {
      LOG.error("unable to load server bookmarks: ", e);
    }

    final var results = new ArrayList<NPPreferenceServerBookmark>();
    for (int index = 0; index < count; ++index) {
      try {
        results.add(this.loadServerBookmark(Integer.valueOf(index)));
      } catch (final Exception e) {
        LOG.error("failed to load server bookmark: ", e);
      }
    }

    LOG.debug("loaded {} server bookmarks", Integer.valueOf(results.size()));
    return List.copyOf(results);
  }

  private NPPreferenceServerBookmark loadServerBookmark(
    final Integer i)
    throws JPropertyNonexistent, JPropertyIncorrectType
  {
    return new NPPreferenceServerBookmark(
      getString(this.properties, String.format("server.bookmarks.%s.name", i)),
      getString(this.properties, String.format("server.bookmarks.%s.host", i)),
      getInteger(this.properties, String.format("server.bookmarks.%s.port", i)),
      this.loadTLS(i),
      this.loadServerBookmarkCredentials(i)
    );
  }

  private NPTLSConfigurationType loadTLS(
    final Integer i)
    throws JPropertyNonexistent, JPropertyIncorrectType
  {
    final var type =
      getString(this.properties,
                String.format("server.bookmarks.%s.tls.type", i));

    return switch (NPTLSConfigurationKind.valueOf(type)) {
      case NPTLSConfigurationKind.TLS_DISABLED -> {
        yield NPTLSDisabled.TLS_DISABLED;
      }

      case NPTLSConfigurationKind.TLS_ENABLED_EXPLICIT -> {
        yield new NPTLSEnabledExplicit(
          new NPTLSStoreConfiguration(
            getString(
              this.properties,
              String.format("server.bookmarks.%s.tls.keyStore.type", i)
            ),
            getString(
              this.properties,
              String.format("server.bookmarks.%s.tls.keyStore.provider", i)
            ),
            getString(
              this.properties,
              String.format("server.bookmarks.%s.tls.keyStore.password", i)
            ),
            this.fileSystem.getPath(getString(
              this.properties,
              String.format("server.bookmarks.%s.tls.keyStore.path", i))
            )
          ),
          new NPTLSStoreConfiguration(
            getString(
              this.properties,
              String.format("server.bookmarks.%s.tls.trustStore.type", i)
            ),
            getString(
              this.properties,
              String.format("server.bookmarks.%s.tls.trustStore.provider", i)
            ),
            getString(
              this.properties,
              String.format("server.bookmarks.%s.tls.trustStore.password", i)
            ),
            this.fileSystem.getPath(getString(
              this.properties,
              String.format("server.bookmarks.%s.tls.trustStore.path", i))
            )
          )
        );
      }

      case NPTLSConfigurationKind.TLS_ENABLED_CLIENT_ANONYMOUS -> {
        yield new NPTLSEnabledClientAnonymous();
      }
    };
  }

  private NPPreferenceServerCredentialsType loadServerBookmarkCredentials(
    final Integer i)
    throws JPropertyNonexistent
  {
    final var value =
      getString(
        this.properties,
        String.format("server.bookmarks.%s.credentials.type", i));

    return switch (value) {
      case "usernamePassword" -> new NPPreferenceServerUsernamePassword(
        getString(
          this.properties,
          String.format("server.bookmarks.%s.credentials.username", i)),
        getString(
          this.properties,
          String.format("server.bookmarks.%s.credentials.password", i))
      );
      default -> throw new IllegalStateException("Unexpected value: " + value);
    };
  }

  @Override
  public String toString()
  {
    return String.format(
      "[NPPreferencesLoader 0x%08x]",
      Integer.valueOf(this.hashCode()));
  }
}
