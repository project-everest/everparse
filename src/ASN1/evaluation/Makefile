all: run

prepare: data

data:
	unzip -u data.zip -d .
	touch $@

run_CRL_positive: prepare
	./run.sh CRL positive

run_CRL_negative: prepare
	./run.sh CRL negative

run_X509_positive: prepare
	./run.sh X509 positive

run_X509_negative: prepare
	./run.sh X509 negative

run: run_X509_negative run_X509_positive run_CRL_negative run_CRL_positive

.PHONY: prepare all run run_X509_negative run_X509_positive run_CRL_negative run_CRL_positive
