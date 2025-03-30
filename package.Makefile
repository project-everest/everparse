# This Makefile is necessary because the main Makefile now requires F*
# to be present.

everparse:
	+src/package/package.sh

.PHONY: everparse

release:
	+src/package/release.sh

.PHONY: release

package:
	+src/package/package.sh -zip

.PHONY: package

package-noversion:
	+src/package/package.sh -zip-noversion -nuget-noversion

.PHONY: package-noversion

# Nuget package only (needed by the Windows workflow, since we let
# GitHub Actions produce the .zip from the everparse directory)
nuget-noversion:
	+src/package/package.sh -nuget-noversion

.PHONY: nuget-noversion
