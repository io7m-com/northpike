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

import net.jqwik.api.providers.ArbitraryProvider;

open module com.io7m.northpike.tests.arbitraries
{
  requires static org.osgi.annotation.bundle;
  requires static org.osgi.annotation.versioning;

  requires net.jqwik.api;
  requires com.io7m.northpike.model;
  requires com.io7m.northpike.protocol.agent;
  requires com.io7m.northpike.protocol.intro;

  uses ArbitraryProvider;

  provides ArbitraryProvider with
com.io7m.northpike.tests.arbitraries.NPArbCommit,
com.io7m.northpike.tests.arbitraries.NPArbCommitAuthor,
com.io7m.northpike.tests.arbitraries.NPArbCommitID,
com.io7m.northpike.tests.arbitraries.NPArbDottedName,
com.io7m.northpike.tests.arbitraries.NPArbErrorCode,
com.io7m.northpike.tests.arbitraries.NPArbKey,
com.io7m.northpike.tests.arbitraries.NPArbOffsetDateTime,
com.io7m.northpike.tests.arbitraries.NPArbRepository,
com.io7m.northpike.tests.arbitraries.NPArbSCMProviderDescription,
com.io7m.northpike.tests.arbitraries.NPArbTimeRange,
com.io7m.northpike.tests.arbitraries.protocol.agent.NPArbACommandLogin,
com.io7m.northpike.tests.arbitraries.protocol.agent.NPArbAMessage,
com.io7m.northpike.tests.arbitraries.protocol.agent.NPArbAResponseError,
com.io7m.northpike.tests.arbitraries.protocol.agent.NPArbAResponseLogin,
com.io7m.northpike.tests.arbitraries.protocol.intro.NPArbIError,
com.io7m.northpike.tests.arbitraries.protocol.intro.NPArbIMessage,
com.io7m.northpike.tests.arbitraries.protocol.intro.NPArbIProtocol,
com.io7m.northpike.tests.arbitraries.protocol.intro.NPArbIProtocolsAvailable
    ;

  exports com.io7m.northpike.tests.arbitraries;
  exports com.io7m.northpike.tests.arbitraries.protocol.agent;
  exports com.io7m.northpike.tests.arbitraries.protocol.intro;
}
