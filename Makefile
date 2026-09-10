PYTHON ?= python3
DRAT_TIMEOUT ?= 90

.PHONY: test check privacy integrity verify verify-full reports reports-en reports-zh figures source-en source-zh package
test:
	$(PYTHON) -B -m unittest discover -s tests -v
check: test
	$(PYTHON) -B tools/check_release.py
privacy:
	$(PYTHON) -B tools/audit_public.py
integrity:
	$(PYTHON) -B proof/verify_proof_package.py
verify:
	$(PYTHON) -B proof/verify_proof_package.py --replay-drat --drat-timeout $(DRAT_TIMEOUT)
verify-full:
	PATH="$(CURDIR)/tools:$(PATH)" $(PYTHON) -B proof/verify_proof_package.py --regenerate-cnf --reexpand-lut --rerun-wang-verifier --drat-timeout $(DRAT_TIMEOUT)
reports:
	$(PYTHON) -B tools/build_reports.py --language all
reports-en:
	$(PYTHON) -B tools/build_reports.py --language en
reports-zh:
	$(PYTHON) -B tools/build_reports.py --language zh
source-en:
	$(PYTHON) -B tools/package_reports.py
source-zh:
	$(PYTHON) -B tools/package_reports.py --language zh
figures:
	$(PYTHON) -B tools/render_figures.py
package:
	$(PYTHON) -B tools/package_release.py
