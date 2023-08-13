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


package com.io7m.northpike.tests.tools.maven;

import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.tools.api.NPToolEventType;
import com.io7m.northpike.tools.api.NPToolException;
import com.io7m.northpike.tools.maven.NPTMFactory3;
import com.io7m.quixote.core.QWebServerType;
import com.io7m.quixote.core.QWebServers;
import com.io7m.repetoir.core.RPServiceDirectory;
import com.io7m.verona.core.Version;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.InputStream;
import java.nio.file.Path;
import java.util.List;
import java.util.Locale;
import java.util.concurrent.Flow;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorIo;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorUnsafeArchiveEntry;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

public final class NPTMFactory3Test implements Flow.Subscriber<NPToolEventType>
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPTMFactory3Test.class);

  private static final Version MAVEN_VERSION =
    Version.of(3, 9, 4);

  private RPServiceDirectory services;
  private NPStrings strings;
  private QWebServerType server;

  @BeforeEach
  public void setup()
    throws Exception
  {
    this.strings = NPStrings.create(Locale.ROOT);
    this.services = new RPServiceDirectory();
    this.services.register(NPStrings.class, this.strings);
    this.server = QWebServers.createServer(30120);
  }

  @AfterEach
  public void tearDown()
    throws Exception
  {
    this.server.close();
  }

  /**
   * Downloads to real servers work.
   *
   * @param directory The output directory
   *
   * @throws Exception On errors
   */

  @Test
  public void testDownloadInstall(
    final @TempDir Path directory)
    throws Exception
  {
    final var tools = new NPTMFactory3();
    try (var tool =
           tools.createTool(this.services, MAVEN_VERSION, directory)) {
      assertTrue(tool.toString().contains("3.9.4"));

      tool.events().subscribe(this);
      tool.install();

      assertTrue(tool.isInstalled());
    }
  }

  /**
   * Hostile tar files are rejected.
   *
   * @param directory The output directory
   *
   * @throws Exception On errors
   */

  @Test
  public void testDownloadInstallHostileTar(
    final @TempDir Path directory)
    throws Exception
  {
    this.server.addResponse()
      .forPath("/maven/maven-3/3.9.4/binaries/apache-maven-3.9.4-bin.tar.gz")
      .withData(resource("hostile.tar.gz"));

    this.server.addResponse()
      .forPath(
        "/maven/maven-3/3.9.4/binaries/apache-maven-3.9.4-bin.tar.gz.sha512")
      .withData(resource("hostile.tar.gz.sha512"));

    final var tools = new NPTMFactory3();
    try (var tool =
           tools.createTool(this.services, MAVEN_VERSION, directory)) {
      tool.events().subscribe(this);
      tool.setHTTPs(false);
      tool.setDownloadHost(
        "%s:%d".formatted(
          this.server.uri().getHost(),
          Integer.valueOf(this.server.uri().getPort())
        )
      );

      final var ex =
        assertThrows(NPToolException.class, tool::install);

      assertEquals(errorUnsafeArchiveEntry(), ex.errorCode());
      assertFalse(tool.isInstalled());
    }
  }

  /**
   * Missing tar files are rejected.
   *
   * @param directory The output directory
   *
   * @throws Exception On errors
   */

  @Test
  public void testDownloadInstallMissingTar(
    final @TempDir Path directory)
    throws Exception
  {
    this.server.addResponse()
      .forPath("/maven/maven-3/3.9.4/binaries/apache-maven-3.9.4-bin.tar.gz")
      .withStatus(404);

    final var tools = new NPTMFactory3();
    try (var tool =
           tools.createTool(this.services, MAVEN_VERSION, directory)) {
      tool.events().subscribe(this);
      tool.setHTTPs(false);
      tool.setDownloadHost(
        "%s:%d".formatted(
          this.server.uri().getHost(),
          Integer.valueOf(this.server.uri().getPort())
        )
      );

      final var ex =
        assertThrows(NPToolException.class, tool::install);

      assertEquals(errorIo(), ex.errorCode());
      assertFalse(tool.isInstalled());
    }
  }

  /**
   * Executing the download tool works.
   *
   * @param directory The output directory
   *
   * @throws Exception On errors
   */

  @Test
  public void testDownloadInstallExecute(
    final @TempDir Path directory)
    throws Exception
  {
    final var tools =
      new NPTMFactory3();

    try (var tool =
           tools.createTool(this.services, MAVEN_VERSION, directory)) {
      tool.events().subscribe(this);
      tool.install();
      assertTrue(tool.isInstalled());

      final var root =
        directory.getRoot();
      final var result =
        tool.execute(root, List.of("--version"));

      assertEquals(0, result.exitCode());
      assertTrue(String.join("\n", result.output()).contains("3.9.4"));
    }
  }


  private static InputStream resource(
    final String name)
  {
    return NPTMFactory3Test.class
      .getResourceAsStream("/com/io7m/northpike/tests/" + name);
  }

  @Override
  public void onSubscribe(
    final Flow.Subscription subscription)
  {
    subscription.request(Long.MAX_VALUE);
  }

  @Override
  public void onNext(
    final NPToolEventType item)
  {
    LOG.debug("{}", item);
  }

  @Override
  public void onError(
    final Throwable throwable)
  {

  }

  @Override
  public void onComplete()
  {

  }
}
