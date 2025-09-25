# This Makefile is necessary because the main Makefile now requires F*
# to be present.

everparse:
	+src/package/package.sh

.PHONY: everparse

package:
	+src/package/package.sh -zip -nuget

.PHONY: package

package-noversion:
	+src/package/package.sh -zip-noversion -nuget-noversion

.PHONY: package-noversion

# Nuget package only (needed by the Windows workflow, since we let
# GitHub Actions produce the .zip from the everparse directory)
nuget:
	+src/package/package.sh -nuget

.PHONY: nuget

nuget-noversion:
	+src/package/package.sh -nuget-noversion

.PHONY: nuget-noversion
