# dummy first rule
git-clone:

.PHONY: git-clone

FStar_hash := master
karamel_hash := master
pulse_hash := main

-include hashes.Makefile

# This rule is necessary for the package and release CI rules to pull
# the right hash when building the F* source package for Windows
echo-FStar-hash:
	echo $(FStar_hash)

.PHONY: echo-FStar-hash

FStar:
ifeq ($(OS),Windows_NT)
	$(error "Cannot build F* from the repository on Windows. Please download and extract a F* source package.")
endif
	rm -rf $@.tmp
	git clone "https://github.com/FStarLang/FStar" $@.tmp
	cd $@.tmp && git checkout $(FStar_hash)
	mv $@.tmp $@

karamel pulse: %:
	rm -rf $@.tmp
	git clone "https://github.com/FStarLang/$@" $@.tmp
	cd $@.tmp && git checkout $($@_hash)
	mv $@.tmp $@

everest:
	git clone "https://github.com/project-everest/everest" $@

clean:
	rm -rf FStar
	rm -rf karamel
	rm -rf pulse

.PHONY: clean

snapshot:
	./snapshot.sh

.PHONY: snapshot

advance:
	+$(MAKE) -f git-clone.Makefile clean
	rm -f hashes.Makefile
	+$(MAKE) -f git-clone.Makefile FStar karamel pulse
	+$(MAKE) -f git-clone.Makefile snapshot

.PHONY: advance
