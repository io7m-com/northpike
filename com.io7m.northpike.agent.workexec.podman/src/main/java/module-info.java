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

import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorFactoryType;
import com.io7m.northpike.agent.workexec.podman.NPWorkExecutorsPodman;

/**
 * Continuous integration (Podman work executor)
 */

module com.io7m.northpike.agent.workexec.podman
{
  requires static org.osgi.annotation.bundle;
  requires static org.osgi.annotation.versioning;

  requires com.io7m.northpike.agent.locks;
  requires com.io7m.northpike.agent.workexec.api;
  requires com.io7m.northpike.agent.workexec.local;
  requires com.io7m.northpike.model;
  requires com.io7m.northpike.protocol.agent.cb;
  requires com.io7m.northpike.protocol.agent;
  requires com.io7m.northpike.strings;

  requires com.io7m.cedarbridge.runtime.api;
  requires com.io7m.cedarbridge.runtime.bssio;
  requires com.io7m.cedarbridge.runtime.convenience;
  requires com.io7m.cedarbridge.runtime.time;
  requires com.io7m.jbssio.vanilla;
  requires com.io7m.jmulticlose.core;
  requires com.io7m.repetoir.core;
  requires com.io7m.tavella.api;
  requires com.io7m.tavella.native_exec;
  requires org.slf4j;

  provides NPAWorkExecutorFactoryType
    with NPWorkExecutorsPodman;

  exports com.io7m.northpike.agent.workexec.podman;
}
