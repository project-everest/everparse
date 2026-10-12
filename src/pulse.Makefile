ifeq (,$(EVERPARSE_HOME))
  $(error "EVERPARSE_HOME must be set to the absolute path of the root of the EverParse repository or installation")
endif

# Which modules or namespaces are already cached? If all of your
# source files in your project are under the same namespace, say
# MyNamespace, then you can set this variable to *,-MyNamespace
ALREADY_CACHED := PulseCore,Pulse,$(ALREADY_CACHED)
