# brick-libcpp

Specifications of the C++ standard library in BRiCk.

## Development

To develop on these specifications, contact Skylabs AI for access to our
verification toolchain, and you a clang toolchain using the GNU C++ library (not
clang's own version).

With access to our release image, you can:
- Open this repo in a devcontainer using our Docker release image; see `.devcontainer/README.md`.

If you have access to our automation sources, you can check this out as part of
https://github.com/SkyLabsAI/workspace. After `make vendored-pull fmdeps-pull`,
you'll find a copy of this repository in `fmdeps/brick-libcpp`. Then:

- on Linux, you can build this directly.
- on any platform, you can route AST generation through our Docker image.
To this end, edit `rocq-brick-libstdcpp/dune` from

```
(env
 (_
  ; Enable the following setting to build ASTs in container.
  ; (env-vars
  ;  (CPP2V_DOCKER_IMAGE "skylabsai/fm-releases:fm-release-nightly"))
```

to

```
(env
 (_
  ; Enable the following setting to build ASTs in container.
  (env-vars
   (CPP2V_DOCKER_IMAGE "skylabsai/fm-releases:fm-release-nightly"))
```
