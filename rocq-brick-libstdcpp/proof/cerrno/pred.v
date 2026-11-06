(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.pred.
Require Export skylabs.brick.libstdcpp.runtime.pred.

(** * The thread-local [errno] object

    C11 7.5p2 makes [errno] an [int] lvalue with thread storage duration;
    C++ [errno] requires it to be a macro. glibc expands it to
    [( *__errno_location ())].

    We model the thread-locality in the _location_: every thread [th] has its
    own [int] object at [errno_loc th], fixed for the lifetime of [th]. Ownership
    [errnoR th q v] is ordinary (objective) memory: handing [&errno] to another
    thread is legal C. Only [current_thread th] (see [runtime.pred]) ties
    [__errno_location] to the calling thread's cell.

    Ownership of [errnoR th 1 _] is provided by the thread's start-up resources
    (the initial thread's [main] precondition, and later [std::thread] entry).
 *)
Parameter errno_loc : thread_idT -> ptr.

#[global] Abbreviation errnoR th q v := (_at (errno_loc th) (intR q v)) (only parsing).
