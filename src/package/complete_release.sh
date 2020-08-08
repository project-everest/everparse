#!/bin/bash

# Upload the release with the tag
LANG=C.UTF-8 LC_ALL=C.UTF-8 satsuki --slug=project-everest/everparse --tag=$everparse_version --file=$archive
