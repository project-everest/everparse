# dummy first rule
git-clone:

.PHONY: git-clone

include hashes.Makefile

EVERPARSE_OPAM_FILES_DEFAULT = fstar-deps.opam everparse-deps.opam
EVERPARSE_OPAM_FILES := $(EVERPARSE_OPAM_FILES_DEFAULT)

# Include specific options on release branches (e.g. EVERPARSE_OPAM_FILES)
-include release.Makefile

ifeq (,$(OPAMNODEPEXTS))
export OPAMNODEPEXTS := 1
endif
ifeq (,$(OPAMYES))
export OPAMYES := 1
endif

cygwin_local_install :=
ifeq ($(OS),Windows_NT)
cygwin_local_install += --cygwin-local-install
endif

# Change these if you want to use your own clones
FStar_repo=https://github.com/FStarLang/FStar

# This rule is necessary for the package and release CI rules to pull
# the right hash when building the F* source package for Windows
echo-FStar-hash:
	echo $(FStar_hash)

.PHONY: echo-FStar-hash

FStar:
ifeq ($(OS),Windows_NT)
	$(error "Cannot build F* from the repository on Windows. Please download and extract a F* source package.")
endif
	git clone $(FStar_repo) $@

opam:
	rm -rf $@ $@.tmp
	if ! opam init $(cygwin_local_install) --no-setup --root=$@ --compiler=5.3.0 ; then mv $@ $@.tmp ; exit 1 ; fi
	touch $@

FStar/Makefile: FStar hashes.Makefile
	if test -d $</.git && ! test -e hashes.lock ; then cd $< && git remote set-url origin $($<_repo) && git fetch && git checkout $($<_hash) ; fi
	touch -c $@
	test -f $@

FStar/karamel/Makefile: FStar/Makefile
	if test -d $(dir $<)/.git && ! test -e hashes.lock ; then cd $(dir $<) && git submodule init && git submodule update && touch -c karamel/Makefile ; else touch -c $@ ; fi

snapshot:
	./snapshot.sh
	touch -c FStar/Makefile

.PHONY: snapshot

fstar-deps.opam: FStar/Makefile
	cp FStar/fstar.opam $@
	touch $@

opam.done: opam $(EVERPARSE_OPAM_FILES)
	eval "$$(opam env --root=opam --set-root)" && opam install --deps-only $(addprefix ./,$(EVERPARSE_OPAM_FILES))
	touch $@

advance:
	rm -f hashes.Makefile
	cp advance.Makefile hashes.Makefile
	touch hashes.Makefile
	+$(MAKE) FStar/Makefile
	+$(MAKE) snapshot

.PHONY: advance

release:
	+$(MAKE) opam.done 'EVERPARSE_OPAM_FILES=$(EVERPARSE_OPAM_FILES_DEFAULT)'
	eval "$$(opam env --root=opam --set-root)" && opam upgrade && opam lock $(addprefix ./,$(EVERPARSE_OPAM_FILES_DEFAULT))

.PHONY: release

FStar.clean:
	rm -f FStar.done
ifeq (,$(do_not_clean_FStar))
	rm -rf FStar
else
	+if test -d FStar ; then $(MAKE) -C FStar clean ; fi
endif

clean_rules := $(addsuffix .clean,z3 opam)

$(clean_rules): %.clean:
	rm -rf $(basename $@) $(basename $@).done

.PHONY: %.clean

clean: FStar.clean $(clean_rules) clean-opam

.PHONY: clean

clean-opam:
	rm -f $(addsuffix -deps.opam,fstar) opam.done

.PHONY: clean-opam
