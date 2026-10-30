# brick-libcpp

Specifications of the C++ standard library in BRiCk.

## Development

To develop on these specifications, you'll need clang, the GNU C++ library (not
clang's own version), and Skylabs AI's verification toolchain.

If you have access to our automation sources, you can check this out as part of
https://github.com/SkyLabsAI/workspace. After `make vendored-pull fmdeps-pull`,
you'll find a copy of this repository in `fmdeps/brick-libcpp`. Build from the
composed workspace root:

```sh
dune build fmdeps/brick-libcpp
```

For Docker-backed builds, see the
[BRiCk Docker setup documentation](https://github.com/SkyLabsAI/BRiCk/blob/main/rocq-skylabs-cpp2v/scripts/README.md).
