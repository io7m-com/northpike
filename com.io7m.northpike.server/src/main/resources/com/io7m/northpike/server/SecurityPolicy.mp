#
# Copyright © 2023 Mark Raynsford <code@io7m.com> https://www.io7m.com
#
# Permission to use, copy, modify, and/or distribute this software for any
# purpose with or without fee is hereby granted, provided that the above
# copyright notice and this permission notice appear in all copies.
#
# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
# WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
# MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
# SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
# WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
# ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR
# IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
#

[Medrina 1 0]

#------------------------------------------------------------------------
# Login
#

[Rule
  [Conclusion   AllowImmediately]
  [MatchSubject [WithAnyRolesFrom login]]
  [MatchObject  [WithType server]]
  [MatchAction  [WithName login]]
]

#------------------------------------------------------------------------
# SCM Providers
#

[Rule
  [Conclusion   AllowImmediately]
  [MatchSubject [WithAnyRolesFrom scm_providers.reader]]
  [MatchObject  [WithType scm_providers]]
  [MatchAction  [WithName read]]
]

[Rule
  [Conclusion   AllowImmediately]
  [MatchSubject [WithAnyRolesFrom scm_providers.writer]]
  [MatchObject  [WithType scm_providers]]
  [MatchAction  [WithName write]]
]

#------------------------------------------------------------------------
# Repositories
#

[Rule
  [Conclusion   AllowImmediately]
  [MatchSubject [WithAnyRolesFrom repositories.reader]]
  [MatchObject  [WithType repositories]]
  [MatchAction  [WithName read]]
]

[Rule
  [Conclusion   AllowImmediately]
  [MatchSubject [WithAnyRolesFrom repositories.writer]]
  [MatchObject  [WithType repositories]]
  [MatchAction  [WithName write]]
]

[Rule
  [Conclusion   AllowImmediately]
  [MatchSubject [WithAllRolesFrom repositories.writer public_keys.reader]]
  [MatchObject  [WithType repositories]]
  [MatchAction  [WithName key_assign]]
]

[Rule
  [Conclusion   AllowImmediately]
  [MatchSubject [WithAllRolesFrom repositories.writer public_keys.reader]]
  [MatchObject  [WithType repositories]]
  [MatchAction  [WithName key_unassign]]
]

#------------------------------------------------------------------------
# Agent Labels
#

[Rule
  [Conclusion   AllowImmediately]
  [MatchSubject [WithAnyRolesFrom agent_labels.reader]]
  [MatchObject  [WithType agent_labels]]
  [MatchAction  [WithName read]]
]

[Rule
  [Conclusion   AllowImmediately]
  [MatchSubject [WithAnyRolesFrom agent_labels.writer]]
  [MatchObject  [WithType agent_labels]]
  [MatchAction  [WithName write]]
]

[Rule
  [Conclusion   AllowImmediately]
  [MatchSubject [WithAnyRolesFrom agent_labels.writer]]
  [MatchObject  [WithType agent_labels]]
  [MatchAction  [WithName delete]]
]

#------------------------------------------------------------------------
# Tools
#

[Rule
  [Conclusion   AllowImmediately]
  [MatchSubject [WithAnyRolesFrom tools.reader]]
  [MatchObject  [WithType tools]]
  [MatchAction  [WithName read]]
]

[Rule
  [Conclusion   AllowImmediately]
  [MatchSubject [WithAnyRolesFrom tools.writer]]
  [MatchObject  [WithType tools]]
  [MatchAction  [WithName write]]
]

#------------------------------------------------------------------------
# Plans
#

[Rule
  [Conclusion   AllowImmediately]
  [MatchSubject [WithAnyRolesFrom plans.reader]]
  [MatchObject  [WithType plans]]
  [MatchAction  [WithName read]]
]

[Rule
  [Conclusion   AllowImmediately]
  [MatchSubject [WithAnyRolesFrom plans.writer]]
  [MatchObject  [WithType plans]]
  [MatchAction  [WithName write]]
]

#------------------------------------------------------------------------
# Agents
#

[Rule
  [Conclusion   AllowImmediately]
  [MatchSubject [WithAnyRolesFrom agents.reader]]
  [MatchObject  [WithType agents]]
  [MatchAction  [WithName read]]
]

[Rule
  [Conclusion   AllowImmediately]
  [MatchSubject [WithAnyRolesFrom agents.writer]]
  [MatchObject  [WithType agents]]
  [MatchAction  [WithName write]]
]

#------------------------------------------------------------------------
# Assignments
#

[Rule
  [Conclusion   AllowImmediately]
  [MatchSubject [WithAnyRolesFrom assignments.reader]]
  [MatchObject  [WithType assignments]]
  [MatchAction  [WithName read]]
]

[Rule
  [Conclusion   AllowImmediately]
  [MatchSubject [WithAnyRolesFrom assignments.writer]]
  [MatchObject  [WithType assignments]]
  [MatchAction  [WithName write]]
]

[Rule
  [Conclusion   AllowImmediately]
  [MatchSubject [WithAnyRolesFrom assignments.executor]]
  [MatchObject  [WithType assignments]]
  [MatchAction  [WithName execute]]
]

[Rule
  [Conclusion   AllowImmediately]
  [MatchSubject [WithAnyRolesFrom assignment_executions.reader]]
  [MatchObject  [WithType assignment_executions]]
  [MatchAction  [WithName read]]
]

[Rule
  [Conclusion   AllowImmediately]
  [MatchSubject [WithAnyRolesFrom assignment_executions.writer]]
  [MatchObject  [WithType assignment_executions]]
  [MatchAction  [WithName delete]]
]

[Rule
  [Conclusion   AllowImmediately]
  [MatchSubject [WithAnyRolesFrom assignment_executions.writer]]
  [MatchObject  [WithType assignment_executions]]
  [MatchAction  [WithName write]]
]

#------------------------------------------------------------------------
# Public Keys
#

[Rule
  [Conclusion   AllowImmediately]
  [MatchSubject [WithAnyRolesFrom public_keys.reader]]
  [MatchObject  [WithType public_keys]]
  [MatchAction  [WithName read]]
]

[Rule
  [Conclusion   AllowImmediately]
  [MatchSubject [WithAnyRolesFrom public_keys.writer]]
  [MatchObject  [WithType public_keys]]
  [MatchAction  [WithName write]]
]

#------------------------------------------------------------------------
# Audit Log
#

[Rule
  [Conclusion   AllowImmediately]
  [MatchSubject [WithAnyRolesFrom audit_log.reader]]
  [MatchObject  [WithType audit_log]]
  [MatchAction  [WithName read]]
]
