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

/**
 * <p>The standard error codes.</p>
 * <p>Note: This file is generated from codes.txt and should not be hand-edited.</p>
 */
public final class NPStandardErrorCodes
{
  private NPStandardErrorCodes()
  {
  }

  private static final NPErrorCode ERROR_API_MISUSE =
    new NPErrorCode("error-api-misuse");

  /**
   * An API was used incorrectly.
   *
   * @return The error code
   */
  public static NPErrorCode errorApiMisuse()
  {
    return ERROR_API_MISUSE;
  }

  private static final NPErrorCode ERROR_AUTHENTICATION =
    new NPErrorCode("error-authentication");

  /**
   * Authentication failed.
   *
   * @return The error code
   */
  public static NPErrorCode errorAuthentication()
  {
    return ERROR_AUTHENTICATION;
  }

  private static final NPErrorCode ERROR_CYCLIC =
    new NPErrorCode("error-cyclic");

  /**
   * A cycle was introduced into a structure that is not supposed to be cyclic.
   *
   * @return The error code
   */
  public static NPErrorCode errorCyclic()
  {
    return ERROR_CYCLIC;
  }

  private static final NPErrorCode ERROR_DUPLICATE =
    new NPErrorCode("error-duplicate");

  /**
   * An object already exists.
   *
   * @return The error code
   */
  public static NPErrorCode errorDuplicate()
  {
    return ERROR_DUPLICATE;
  }

  private static final NPErrorCode ERROR_HTTP_METHOD =
    new NPErrorCode("error-http-method");

  /**
   * The wrong HTTP method was used.
   *
   * @return The error code
   */
  public static NPErrorCode errorHttpMethod()
  {
    return ERROR_HTTP_METHOD;
  }

  private static final NPErrorCode ERROR_IO =
    new NPErrorCode("error-io");

  /**
   * An internal I/O error.
   *
   * @return The error code
   */
  public static NPErrorCode errorIo()
  {
    return ERROR_IO;
  }

  private static final NPErrorCode ERROR_NONEXISTENT =
    new NPErrorCode("error-nonexistent");

  /**
   * A requested object was not found.
   *
   * @return The error code
   */
  public static NPErrorCode errorNonexistent()
  {
    return ERROR_NONEXISTENT;
  }

  private static final NPErrorCode ERROR_NOT_LOGGED_IN =
    new NPErrorCode("error-not-logged-in");

  /**
   * A user is trying to perform an operation without having logged in.
   *
   * @return The error code
   */
  public static NPErrorCode errorNotLoggedIn()
  {
    return ERROR_NOT_LOGGED_IN;
  }

  private static final NPErrorCode ERROR_NO_SUPPORTED_PROTOCOLS =
    new NPErrorCode("error-no-supported-protocols");

  /**
   * The client and server have no supported protocols in common.
   *
   * @return The error code
   */
  public static NPErrorCode errorNoSupportedProtocols()
  {
    return ERROR_NO_SUPPORTED_PROTOCOLS;
  }

  private static final NPErrorCode ERROR_OPERATION_NOT_PERMITTED =
    new NPErrorCode("error-operation-not-permitted");

  /**
   * A generic "operation not permitted" error.
   *
   * @return The error code
   */
  public static NPErrorCode errorOperationNotPermitted()
  {
    return ERROR_OPERATION_NOT_PERMITTED;
  }

  private static final NPErrorCode ERROR_PARSE =
    new NPErrorCode("error-parse");

  /**
   * A parse error was encountered.
   *
   * @return The error code
   */
  public static NPErrorCode errorParse()
  {
    return ERROR_PARSE;
  }

  private static final NPErrorCode ERROR_PROTOCOL =
    new NPErrorCode("error-protocol");

  /**
   * A client sent a broken message of some kind.
   *
   * @return The error code
   */
  public static NPErrorCode errorProtocol()
  {
    return ERROR_PROTOCOL;
  }

  private static final NPErrorCode ERROR_REMOVE_TOO_MANY_ITEMS =
    new NPErrorCode("error-remove-too-many-items");

  /**
   * An attempt was made to remove more items than actually exist.
   *
   * @return The error code
   */
  public static NPErrorCode errorRemoveTooManyItems()
  {
    return ERROR_REMOVE_TOO_MANY_ITEMS;
  }

  private static final NPErrorCode ERROR_RESOURCE_CLOSE_FAILED =
    new NPErrorCode("error-resource-close-failed");

  /**
   * One or more resources failed to close.
   *
   * @return The error code
   */
  public static NPErrorCode errorResourceCloseFailed()
  {
    return ERROR_RESOURCE_CLOSE_FAILED;
  }

  private static final NPErrorCode ERROR_SECURITY_POLICY_DENIED =
    new NPErrorCode("error-security-policy-denied");

  /**
   * An operation was denied by the security policy.
   *
   * @return The error code
   */
  public static NPErrorCode errorSecurityPolicyDenied()
  {
    return ERROR_SECURITY_POLICY_DENIED;
  }

  private static final NPErrorCode ERROR_SQL_FOREIGN_KEY =
    new NPErrorCode("error-sql-foreign-key");

  /**
   * A violation of an SQL foreign key integrity constraint.
   *
   * @return The error code
   */
  public static NPErrorCode errorSqlForeignKey()
  {
    return ERROR_SQL_FOREIGN_KEY;
  }

  private static final NPErrorCode ERROR_SQL_REVISION =
    new NPErrorCode("error-sql-revision");

  /**
   * An internal SQL database error relating to database revisioning.
   *
   * @return The error code
   */
  public static NPErrorCode errorSqlRevision()
  {
    return ERROR_SQL_REVISION;
  }

  private static final NPErrorCode ERROR_SQL_UNIQUE =
    new NPErrorCode("error-sql-unique");

  /**
   * A violation of an SQL uniqueness constraint.
   *
   * @return The error code
   */
  public static NPErrorCode errorSqlUnique()
  {
    return ERROR_SQL_UNIQUE;
  }

  private static final NPErrorCode ERROR_SQL_UNSUPPORTED_QUERY_CLASS =
    new NPErrorCode("error-sql-unsupported-query-class");

  /**
   * An attempt was made to use a query class that is unsupported.
   *
   * @return The error code
   */
  public static NPErrorCode errorSqlUnsupportedQueryClass()
  {
    return ERROR_SQL_UNSUPPORTED_QUERY_CLASS;
  }

  private static final NPErrorCode ERROR_SQL =
    new NPErrorCode("error-sql");

  /**
   * An internal SQL database error.
   *
   * @return The error code
   */
  public static NPErrorCode errorSql()
  {
    return ERROR_SQL;
  }

  private static final NPErrorCode ERROR_TRASCO =
    new NPErrorCode("error-trasco");

  /**
   * An error raised by the Trasco database versioning library.
   *
   * @return The error code
   */
  public static NPErrorCode errorTrasco()
  {
    return ERROR_TRASCO;
  }

  private static final NPErrorCode ERROR_TYPE_CHECK_FAILED =
    new NPErrorCode("error-type-check-failed");

  /**
   * Type checking failed.
   *
   * @return The error code
   */
  public static NPErrorCode errorTypeCheckFailed()
  {
    return ERROR_TYPE_CHECK_FAILED;
  }

  private static final NPErrorCode ERROR_TYPE_CHECK_FIELD_INVALID =
    new NPErrorCode("error-type-field-invalid");

  /**
   * A field value did not match the provided pattern.
   *
   * @return The error code
   */
  public static NPErrorCode errorTypeCheckFieldInvalid()
  {
    return ERROR_TYPE_CHECK_FIELD_INVALID;
  }

  private static final NPErrorCode ERROR_TYPE_CHECK_FIELD_PATTERN_FAILURE =
    new NPErrorCode("error-type-field-pattern-invalid");

  /**
   * A field pattern was invalid.
   *
   * @return The error code
   */
  public static NPErrorCode errorTypeCheckFieldPatternFailure()
  {
    return ERROR_TYPE_CHECK_FIELD_PATTERN_FAILURE;
  }

  private static final NPErrorCode ERROR_TYPE_CHECK_FIELD_REQUIRED_MISSING =
    new NPErrorCode("error-type-field-required-missing");

  /**
   * A field was required but is missing.
   *
   * @return The error code
   */
  public static NPErrorCode errorTypeCheckFieldRequiredMissing()
  {
    return ERROR_TYPE_CHECK_FIELD_REQUIRED_MISSING;
  }

  private static final NPErrorCode ERROR_TYPE_FIELD_TYPE_NONEXISTENT =
    new NPErrorCode("error-type-field-type-nonexistent");

  /**
   * A field in the type declaration refers to a nonexistent type.
   *
   * @return The error code
   */
  public static NPErrorCode errorTypeFieldTypeNonexistent()
  {
    return ERROR_TYPE_FIELD_TYPE_NONEXISTENT;
  }

  private static final NPErrorCode ERROR_TYPE_REFERENCED =
    new NPErrorCode("error-type-referenced");

  /**
   * The type is referenced by one or more existing items.
   *
   * @return The error code
   */
  public static NPErrorCode errorTypeReferenced()
  {
    return ERROR_TYPE_REFERENCED;
  }

  private static final NPErrorCode ERROR_TYPE_SCALAR_REFERENCED =
    new NPErrorCode("error-type-scalar-referenced");

  /**
   * The scalar type is referenced by one or more existing types/fields.
   *
   * @return The error code
   */
  public static NPErrorCode errorTypeScalarReferenced()
  {
    return ERROR_TYPE_SCALAR_REFERENCED;
  }

  private static final NPErrorCode ERROR_UNSAFE_ARCHIVE_ENTRY =
    new NPErrorCode("error-unsafe-archive-entry");

  /**
   * An unsafe archive entry was encountered.
   *
   * @return The error code
   */
  public static NPErrorCode errorUnsafeArchiveEntry()
  {
    return ERROR_UNSAFE_ARCHIVE_ENTRY;
  }

  private static final NPErrorCode ERROR_UNSUPPORTED =
    new NPErrorCode("error-unsupported");

  /**
   * An operation was unsupported.
   *
   * @return The error code
   */
  public static NPErrorCode errorUnsupported()
  {
    return ERROR_UNSUPPORTED;
  }

  private static final NPErrorCode ERROR_USER_NONEXISTENT =
    new NPErrorCode("error-user-nonexistent");

  /**
   * An attempt was made to reference a user that does not exist.
   *
   * @return The error code
   */
  public static NPErrorCode errorUserNonexistent()
  {
    return ERROR_USER_NONEXISTENT;
  }

  private static final NPErrorCode ERROR_COMPILATION_FAILED =
    new NPErrorCode("error-compilation-failed");

  /**
   * Compilation failed.
   *
   * @return The error code
   */
  public static NPErrorCode errorCompilationFailed()
  {
    return ERROR_COMPILATION_FAILED;
  }

  private static final NPErrorCode ERROR_SIGNATURE_VERIFICATION_FAILED =
    new NPErrorCode("error-signature-verification-failed");

  /**
   * Signature verification failed.
   *
   * @return The error code
   */
  public static NPErrorCode errorSignatureVerificationFailed()
  {
    return ERROR_SIGNATURE_VERIFICATION_FAILED;
  }

  private static final NPErrorCode ERROR_PLAN_STILL_REFERENCED =
    new NPErrorCode("error-plan-still-referenced");

  /**
   * The given plan cannot be deleted because it is still referenced by one or more assignments.
   *
   * @return The error code
   */
  public static NPErrorCode errorPlanStillReferenced()
  {
    return ERROR_PLAN_STILL_REFERENCED;
  }

  private static final NPErrorCode ERROR_TOOL_EXECUTION_STILL_REFERENCED =
    new NPErrorCode("error-tool-execution-still-referenced");

  /**
   * The tool execution cannot be deleted because it is still referenced by one or more plans.
   *
   * @return The error code
   */
  public static NPErrorCode errorToolExecutionStillReferenced()
  {
    return ERROR_TOOL_EXECUTION_STILL_REFERENCED;
  }
}

