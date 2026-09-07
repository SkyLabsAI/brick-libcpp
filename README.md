# brick-libcpp

Specifications of the C++ standard library in BRiCk.

## Development

To develop on these specifications, you'll need clang, the GNU C++ library (not
clang's own version), and Skylabs AI's verification toolchain.

With access to our release image, you can:
- Open this repo in a devcontainer using our Docker release image; see `.devcontainer/README.md`.

If you have access to our automation sources, you can check this out as part of
https://github.com/SkyLabsAI/workspace. After `make vendored-pull fmdeps-pull`,
you'll find a copy of this repository in `fmdeps/brick-libcpp`. Then:

- on Linux with a suitable clang + GNU C++ library toolchain, you can build this
  directly.
- on any platform, you can route AST generation through our Docker image. Use
  this route when local AST generation fails because libstdc++ headers such as
  `<cassert>` cannot be found.

To enable Docker-backed AST generation in the composed workspace, go to
`workspace` and run
```
cd fmdeps/brick-libcpp; cp dune.disabled dune
```

The copied `dune` file is a local, ignored opt-in. It makes Dune use
`rocq-brick-libstdcpp/cpp2v_docker` as `cpp2v` for the libstdc++ specs and
tests, so Docker must be running and accessible to the build.

The setup can be especially useful when one needs to use `libstdc++`
which is not available on all platforms. To reduce demands on the
docker virtual machines, one can enable its use selectively. See
`rocq-brick-libstdcpp/cpp2v_docker.in` for more details.
