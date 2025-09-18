# dummy first rule
git-clone:

.PHONY: git-clone

include hashes.Makefile

# Change these if you want to use your own clones
FStar_repo=https://github.com/FStarLang/FStar
karamel_repo=https://github.com/FStarLang/karamel
pulse_repo=https://github.com/FStarLang/pulse

# This rule is necessary for the package and release CI rules to pull
# the right hash when building the F* source package for Windows
echo-FStar-hash:
	echo $(FStar_hash)

.PHONY: echo-FStar-hash

FStar:
ifeq ($(OS),Windows_NT)
	$(error "Cannot build F* from the repository on Windows. Please download and extract a F* source package.")
endif
	git clone $(FStar_repo)

karamel pulse: %:
	git clone $($@_repo) $@

%/Makefile: % hashes.Makefile
	if test -d $</.git ; then cd $< && git remote set-url origin $($<_repo) && git fetch && git checkout $($<_hash) ; fi
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
	+$(MAKE) FStar/Makefile karamel/Makefile pulse/Makefile
	+$(MAKE) snapshot

.PHONY: advance
