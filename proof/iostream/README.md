# `<iostream>`

This directory captures the behavior of the `<iostream>` library using the refinement methodology
developed in the [Spectra](https://github.com/SkyLabsAI/BRiCk/blob/main/rocq-skylabs-iris/theories/base_logic/lib/spectra.md) library.

At the high level, the behavior of a program is described by a labled transition system (LTS** and the
*current state* of the LTS is embedded in separation logic (in Spectra this is done using `AuthSet.frag`).
Interactions with the outside world are captured via updating this state through the use of requesters
and committers which allow updating this state by emitting appropriate events.

## Adequacy

See the Spectra docs for more information about establishing a formal refinement with this setup.

## References

- [Spectra](https://github.com/SkyLabsAI/BRiCk/blob/main/rocq-skylabs-iris/theories/base_logic/lib/spectra.md)
- [A Separation Logic for Refining Concurrent Objects](https://dl.acm.org/doi/10.1145/1926385.1926415)
