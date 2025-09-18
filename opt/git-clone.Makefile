# dummy first rule
git-clone:

.PHONY: git-clone

include hashes.Makefile

# This rule is necessary for the package and release CI rules to pull
# the right hash when building the F* source package for Windows
echo-FStar-hash:
	echo $(FStar_hash)

.PHONY: echo-FStar-hash

FStar:
ifeq ($(OS),Windows_NT)
	$(error "Cannot build F* from the repository on Windows. Please download and extract a F* source package.")
endif
	git clone "https://github.com/FStarLang/FStar"

karamel pulse: %:
	git clone "https://github.com/FStarLang/$@" $@

%/Makefile: % hashes.Makefile
	if test -d $</.git ; then cd $< && git fetch && git checkout $($<_hash) ; fi
	touch -c $@
	test -f $@

everest:
	git clone "https://github.com/project-everest/everest" $@

snapshot:
	./snapshot.sh
	touch -c FStar/Makefile karamel/Makefile pulse/Makefile

.PHONY: snapshot

advance:
	rm -f hashes.Makefile
	cp advance.Makefile hashes.Makefile
	touch hashes.Makefile
	+$(MAKE) -f git-clone.Makefile FStar/Makefile karamel/Makefile pulse/Makefile
	+$(MAKE) -f git-clone.Makefile snapshot

.PHONY: advance
