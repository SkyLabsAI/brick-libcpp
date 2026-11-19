(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(* The process and target generations are shared with pthread_create. *)
Require Export skylabs.brick.libstdcpp.pthread.create.model.

Module pthread_join.
  (** Process setup and the application supply a conservative bound on the
      nonempty direct or transitive wait-for paths that can occur while a
      proposed join is outstanding, including waits executed by callbacks.
      The paths describe dependencies apart from the proposed join edge.
      The correspondence to the application's possible executions is a
      rely condition on this bound. It is independent of the ID registry. *)
  Class ProcessWaitDiscipline := {
    may_wait_path : thread_idT -> thread_idT -> Prop;
  }.
End pthread_join.
