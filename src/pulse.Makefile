ifeq (,$(EVERPARSE_SRC_PATH))
  $(error "EVERPARSE_SRC_PATH must be set to the absolute path of the src/ subdirectory of the EverParse repository")
endif

# Which modules or namespaces are already cached? If all of your
# source files in your project are under the same namespace, say
# MyNamespace, then you can set this variable to *,-MyNamespace
ALREADY_CACHED := PulseCore,Pulse,$(ALREADY_CACHED)
