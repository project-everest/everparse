all:
	+$(MAKE) prepare
	+$(MAKE) run

prepare:
	unzip -u data.zip -d .

run_CRL_positive:
	./run.sh CRL positive

run_CRL_negative:
	./run.sh CRL negative

run_X509_positive:
	./run.sh X509 positive

run_X509_negative:
	./run.sh X509 negative

run: run_X509_negative run_X509_positive run_CRL_negative run_CRL_positive

.PHONY: prepare all run run_X509_negative run_X509_positive run_CRL_negative run_CRL_positive
