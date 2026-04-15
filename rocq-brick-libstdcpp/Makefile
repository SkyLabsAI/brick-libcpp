.PHONY: proof/dune.inc

proof: proof/dune.inc
	dune b

proof/dune.inc:
	dune b @dune_inc --auto-promote || true
# The --auto-promote option will automatically update the .inc file with the new
# build rule _and fail if any change is needed_, so we ignore the failure.

