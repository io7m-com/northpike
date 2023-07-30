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


package com.io7m.northpike.model;

import org.jgrapht.graph.AsUnmodifiableGraph;
import org.jgrapht.graph.DirectedAcyclicGraph;
import org.jgrapht.graph.GraphCycleProhibitedException;

import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * The graph formed by a set of commits.
 */

public final class NPCommitGraph
{
  private final AsUnmodifiableGraph<NPCommitID, NPCommitLink> linksPrevious;
  private final AsUnmodifiableGraph<NPCommitID, NPCommitLink> linksNext;
  private final Set<NPCommitLink> linksByCommit;

  private NPCommitGraph(
    final AsUnmodifiableGraph<NPCommitID, NPCommitLink> inLinksPrevious,
    final AsUnmodifiableGraph<NPCommitID, NPCommitLink> inLinksNext,
    final Set<NPCommitLink> inLinksByCommit)
  {
    this.linksPrevious =
      Objects.requireNonNull(inLinksPrevious, "linksPrevious");
    this.linksNext =
      Objects.requireNonNull(inLinksNext, "linksNext");
    this.linksByCommit =
      Objects.requireNonNull(inLinksByCommit, "linksByCommit");
  }

  /**
   * @return The graph linking each commit to its previous commit
   */

  public AsUnmodifiableGraph<NPCommitID, NPCommitLink> linksPrevious()
  {
    return this.linksPrevious;
  }

  /**
   * @return The graph linking each commit to its next commit
   */

  public AsUnmodifiableGraph<NPCommitID, NPCommitLink> linksNext()
  {
    return this.linksNext;
  }

  /**
   * @return The links by commit ID
   */

  public Set<NPCommitLink> linksByCommit()
  {
    return this.linksByCommit;
  }

  /**
   * Create a graph from the given commit links.
   *
   * @param links The links
   *
   * @return A created graph
   *
   * @throws NPException On graph cycles
   */

  public static NPCommitGraph create(
    final Set<NPCommitLink> links)
    throws NPException
  {
    final var graphNext =
      new DirectedAcyclicGraph<NPCommitID, NPCommitLink>(NPCommitLink.class);
    final var graphPrev =
      new DirectedAcyclicGraph<NPCommitID, NPCommitLink>(NPCommitLink.class);

    for (final var link : links) {
      try {
        graphNext.addVertex(link.commit());
        graphPrev.addVertex(link.commit());

        link.next()
          .ifPresent(next -> {
            graphNext.addVertex(next);
            graphPrev.addVertex(next);
            graphNext.addEdge(link.commit(), next, link);
            graphPrev.addEdge(next, link.commit(), link);
          });

      } catch (final GraphCycleProhibitedException e) {
        throw new NPException(
          e.getMessage(),
          NPStandardErrorCodes.errorCyclic(),
          Map.of(),
          Optional.empty()
        );
      }
    }

    return new NPCommitGraph(
      new AsUnmodifiableGraph<>(graphPrev),
      new AsUnmodifiableGraph<>(graphNext),
      Set.copyOf(links)
    );
  }
}
