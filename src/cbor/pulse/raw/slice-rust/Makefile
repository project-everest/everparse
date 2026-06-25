all: verify

# Local build of the Rust-backend implementation of the byte_slice seam
# (CBOR.Pulse.Raw.Slice). The seam's interface (../CBOR.Pulse.Raw.Slice.fsti) is
# abstract; its two backend .fst implementations (slice-c, slice-rust) realize
# byte_slice0 differently and share the same module name, so they cannot coexist
# in a single dependency scan and are excluded from the global checked-file cache.
# Each backend therefore lives in its own directory with this Makefile, which
# builds just its CBOR.Pulse.Raw.Slice.fst.checked. The shared .fsti.checked and
# the rest of the CBOR closure must already be checked (see `cbor-verify-aux` in
# the repository-root Makefile) before this runs.
EVERPARSE_SRC_PATH = $(realpath ../../../..)
INCLUDE_PATHS += $(realpath ..)
ALREADY_CACHED := *,-CBOR.Pulse.Raw.Slice,

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile
