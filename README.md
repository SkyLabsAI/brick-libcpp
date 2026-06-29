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
To this end, go to `workspace` and run
```
cd fmdeps/brick-libcpp; cp dune.disabled dune
```
The setup can be especially useful when one needs to use `libstdc++`
which is not available on all platforms. To reduce demands on the
docker virtual machines, one can enable its use selectively. See
`rocq-brick-libstdcpp/cpp2v_docker.in` for more details.
