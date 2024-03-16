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


package com.io7m.northpike.tests.agent;

import com.io7m.anethum.slf4j.ParseStatusLogging;
import com.io7m.northpike.agent.NPAgentHosts;
import com.io7m.northpike.agent.api.NPAgentHostConfiguration;
import com.io7m.northpike.agent.configuration.NPACFiles;
import com.io7m.northpike.agent.configuration.NPACPreserveLexical;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.slf4j.bridge.SLF4JBridgeHandler;

import java.nio.file.Paths;

public final class NPAgentDemo
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgentDemo.class);

  private NPAgentDemo()
  {

  }

  public static void main(
    final String[] args)
    throws Exception
  {
    System.setProperty("org.jooq.no-tips", "true");
    System.setProperty("org.jooq.no-logo", "true");

    SLF4JBridgeHandler.removeHandlersForRootLogger();
    SLF4JBridgeHandler.install();

    final var configurationParsers =
      new NPACFiles();

    final NPAgentHostConfiguration configuration =
      configurationParsers.parseFileWithContext(
        NPACPreserveLexical.PRESERVE_LEXICAL_INFORMATION,
        Paths.get("agent.xml"),
        status -> ParseStatusLogging.logWithAll(LOG, status)
      );

    final var agentHosts = new NPAgentHosts();
    try (var agentHost = agentHosts.createHost(configuration)) {
      agentHost.start();


    }
  }
}
