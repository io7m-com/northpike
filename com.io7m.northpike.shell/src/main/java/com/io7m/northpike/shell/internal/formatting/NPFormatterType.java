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

package com.io7m.northpike.shell.internal.formatting;

import com.io7m.northpike.model.NPAgentDescription;
import com.io7m.northpike.model.NPAgentID;
import com.io7m.northpike.model.NPAgentLabel;
import com.io7m.northpike.model.NPAgentSummary;
import com.io7m.northpike.model.NPAuditEvent;
import com.io7m.northpike.model.NPFingerprint;
import com.io7m.northpike.model.NPPage;
import com.io7m.northpike.model.NPPublicKey;
import com.io7m.northpike.model.NPRepositoryDescription;
import com.io7m.northpike.model.NPRepositorySummary;
import com.io7m.northpike.model.NPSCMProviderDescription;
import com.io7m.northpike.model.NPToolExecutionDescription;
import com.io7m.northpike.model.NPToolExecutionDescriptionSummary;
import com.io7m.northpike.model.NPUser;
import com.io7m.northpike.model.NPWorkItem;
import com.io7m.northpike.model.plans.NPPlanDescriptionUnparsed;
import com.io7m.northpike.model.plans.NPPlanSummary;

import java.util.Set;
import java.util.UUID;

/**
 * A shell formatter for data.
 */

public interface NPFormatterType
{
  /**
   * Format a page of audit events.
   *
   * @param page The page
   *
   * @throws Exception On errors
   */

  void formatAudits(
    NPPage<NPAuditEvent> page)
    throws Exception;

  /**
   * Format a repository.
   *
   * @param repository The repository
   *
   * @throws Exception On errors
   */

  void formatRepository(
    NPRepositoryDescription repository)
    throws Exception;

  /**
   * Format a page of repository summaries.
   *
   * @param page The page
   *
   * @throws Exception On errors
   */

  void formatRepositorySummaries(
    NPPage<NPRepositorySummary> page)
    throws Exception;

  /**
   * Format a public key.
   *
   * @param key The key
   *
   * @throws Exception On errors
   */

  void formatPublicKey(NPPublicKey key)
    throws Exception;

  /**
   * Format public key summaries.
   *
   * @param page The keys
   *
   * @throws Exception On errors
   */

  void formatPublicKeySummaries(NPPage<NPPublicKey> page)
    throws Exception;

  /**
   * Format public key fingerprints.
   *
   * @param keys The keys
   *
   * @throws Exception On errors
   */

  void formatFingerprints(Set<NPFingerprint> keys)
    throws Exception;

  /**
   * Format the SCM providers.
   *
   * @param providers The providers
   *
   * @throws Exception On errors
   */

  void formatSCMProviders(
    Set<NPSCMProviderDescription> providers)
    throws Exception;

  /**
   * Format the given user ID.
   *
   * @param id The user
   *
   * @throws Exception On errors
   */

  void formatUserID(UUID id)
    throws Exception;

  /**
   * Format user summaries.
   *
   * @param users The users
   *
   * @throws Exception On errors
   */

  void formatUsers(NPPage<NPUser> users)
    throws Exception;

  /**
   * Format an agent.
   *
   * @param agent The agent
   *
   * @throws Exception On errors
   */

  void formatAgent(
    NPAgentDescription agent)
    throws Exception;

  /**
   * Format agent summaries.
   *
   * @param agents The agents
   *
   * @throws Exception On errors
   */

  void formatAgentSummaries(
    NPPage<NPAgentSummary> agents)
    throws Exception;

  /**
   * Format an agent label.
   *
   * @param label The label
   *
   * @throws Exception On errors
   */

  void formatAgentLabel(
    NPAgentLabel label)
    throws Exception;

  /**
   * Format agent labels.
   *
   * @param page The page
   *
   * @throws Exception On errors
   */

  void formatAgentLabels(
    NPPage<NPAgentLabel> page)
    throws Exception;

  /**
   * Format tool execution description summaries.
   *
   * @param page The tool execution descriptions
   *
   * @throws Exception On errors
   */

  void formatToolExecutionDescriptionSummaries(
    NPPage<NPToolExecutionDescriptionSummary> page)
    throws Exception;

  /**
   * Format a tool execution description.
   *
   * @param data The tool execution description
   *
   * @throws Exception On errors
   */

  void formatToolExecutionDescription(
    NPToolExecutionDescription data)
    throws Exception;

  /**
   * Format a plan.
   *
   * @param plan The data
   *
   * @throws Exception On errors
   */

  void formatPlan(
    NPPlanDescriptionUnparsed plan)
    throws Exception;

  /**
   * Format plan summaries.
   *
   * @param page The plan descriptions
   *
   * @throws Exception On errors
   */

  void formatPlanSummaries(
    NPPage<NPPlanSummary> page)
    throws Exception;

  /**
   * Format agent IDs.
   *
   * @param agents The IDs
   *
   * @throws Exception On errors
   */

  void formatAgentIDs(
    Set<NPAgentID> agents)
    throws Exception;

  /**
   * Format work items.
   *
   * @param workItems The work items
   *
   * @throws Exception On errors
   */

  void formatWorkItems(
    Set<NPWorkItem> workItems)
    throws Exception;

}
