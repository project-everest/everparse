# dummy first rule
git-clone:

.PHONY: git-clone

FStar:
ifeq ($(OS),Windows_NT)
	$(error "Cannot build F* from the repository on Windows. Please download and extract a F* source package.")
endif
	git clone "https://github.com/FStarLang/FStar" $@

karamel:
	git clone "https://github.com/FStarLang/karamel" $@

pulse:
	git clone "https://github.com/FStarLang/pulse" $@

everest:
	git clone "https://github.com/project-everest/everest" $@
