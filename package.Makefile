# This Makefile is necessary because the main Makefile now requires F*
# to be present.

everparse:
	+src/package/package.sh -make

.PHONY: everparse

release:
	+src/package/release.sh

.PHONY: release

package:
	+src/package/package.sh -zip

.PHONY: package

package-noversion:
	+src/package/package.sh -zip-noversion

.PHONY: package-noversion
