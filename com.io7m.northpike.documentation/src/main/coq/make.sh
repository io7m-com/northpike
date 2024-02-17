#!/bin/sh -ex

coqc -Q Northpike Northpike Northpike/TotalMap.v
coqc -Q Northpike Northpike Northpike/Plan/Parameters.v
coqc -Q Northpike Northpike Northpike/Plan/AgentConstraints.v
coqc -Q Northpike Northpike Northpike/Plan/Example.v
coqc -Q Northpike Northpike Northpike/Plan/State.v
coqc -Q Northpike Northpike Northpike/Plan/Initial.v
coqc -Q Northpike Northpike Northpike/Plan/Transition.v
coqc -Q Northpike Northpike Northpike/Plan/TransitionWaitingDependencies.v
coqc -Q Northpike Northpike Northpike/Plan/TransitionDependencyFailed.v
coqc -Q Northpike Northpike Northpike/Plan/TransitionDependencyReady.v
coqc -Q Northpike Northpike Northpike/Plan/TransitionAgentStart.v
coqc -Q Northpike Northpike Northpike/Plan/TransitionAgentContinue.v
coqc -Q Northpike Northpike Northpike/Plan/TransitionAgentTimedOut.v
coqc -Q Northpike Northpike Northpike/Plan/TransitionAgentTaskAccepted.v
coqc -Q Northpike Northpike Northpike/Plan/TransitionAgentTaskStarted.v
coqc -Q Northpike Northpike Northpike/Plan/TransitionAgentTaskContinue.v
coqc -Q Northpike Northpike Northpike/Plan/TransitionAgentTaskTimedOut.v
coqc -Q Northpike Northpike Northpike/Plan/TransitionAgentTaskSucceeded.v
coqc -Q Northpike Northpike Northpike/Plan/TransitionAgentTaskFailed.v
coqc -Q Northpike Northpike Northpike/Plan/TransitionAgentTaskFinishedButTimedOut.v
coqc -Q Northpike Northpike Northpike/Plan/TransitionAgentTaskSucceededIdle.v
coqc -Q Northpike Northpike Northpike/Plan/TransitionAgentTaskFailedIdle.v
coqc -Q Northpike Northpike Northpike/Plan/TransitionBarrierSucceeds.v
coqc -Q Northpike Northpike Northpike/Plan/Completion.v
coqc -Q Northpike Northpike Northpike/Plan/Execution.v

mkdir -p html

coqdoc -Q Northpike Northpike --utf8 -d html $(find Northpike -type f -name '*.v')
