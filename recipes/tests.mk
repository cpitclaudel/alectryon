# -*- makefile -*-
### Auto-generated with etc/regen_makefile.py ###
### Do not edit! ###

_output/tests/:
	mkdir -p $@

tests_targets :=

# CLIs
_output/tests/alternative_clis.out: tests/alternative_clis.py | _output/tests/
	$(PYTHON) $< > $@
tests_targets += _output/tests/alternative_clis.out

# reST → HTML
_output/tests/auto_toggle.html: tests/auto_toggle.rst
	$(alectryon) $<
tests_targets += _output/tests/auto_toggle.html

# Coq → HTML (cached)
_output/tests/cache_v1.html: tests/cache_v1.v
	$(alectryon) $< --cache-directory tests/
tests_targets += _output/tests/cache_v1.html

# Coq → HTML (cached)
_output/tests/cache_v2.html: tests/cache_v2.v
	$(alectryon) $< --cache-directory tests/
tests_targets += _output/tests/cache_v2.html

# reST + assertions
_output/tests/cli_flags.txt: tests/cli_flags.rst
	$(alectryon) $< -o - >/dev/null --debug --traceback --expect-unexpected --long-line-threshold=-1 -I . -R ../recipes/ custom_flag_recipes -Q ../alectryon/ custom_flag_alectryon_tests; echo "exit: $$?" > $@
tests_targets += _output/tests/cli_flags.txt

# ReST → HTML
_output/tests/coqc_time_error.out: tests/coqc_time_error.rst
	$(alectryon) --coq-driver=coqc_time $< > $@ 2>&1; echo "exit: $$?" >> $@
tests_targets += _output/tests/coqc_time_error.out

# Lean → HTML
_output/tests/corner_cases.lean.html: tests/corner_cases.lean
	$(alectryon) $< -o $@
tests_targets += _output/tests/corner_cases.lean.html

# Coq → HTML
_output/tests/corner_cases.html: tests/corner_cases.rst
	$(alectryon) --stdin-filename $< --frontend rst -o $@ - < $<
tests_targets += _output/tests/corner_cases.html
# Coq → LaTeX
_output/tests/corner_cases.xe.tex: tests/corner_cases.rst
	$(alectryon) $< -o $@ --latex-dialect xelatex
tests_targets += _output/tests/corner_cases.xe.tex

# HTML4
_output/tests/dialects.4.html: tests/dialects.rst
	$(alectryon) --html-dialect=html4 -o $@ $<
tests_targets += _output/tests/dialects.4.html
# HTML5
_output/tests/dialects.5.html: tests/dialects.rst
	$(alectryon) --html-dialect=html5 -o $@ $<
tests_targets += _output/tests/dialects.5.html
# LaTeX
_output/tests/dialects.tex: tests/dialects.rst
	$(alectryon) --latex-dialect=pdflatex -o $@ $<
tests_targets += _output/tests/dialects.tex
# XeLaTeX
_output/tests/dialects.xe.tex: tests/dialects.rst
	$(alectryon) --latex-dialect=xelatex -o $@ $<
tests_targets += _output/tests/dialects.xe.tex
# LuaLaTeX
_output/tests/dialects.lua.tex: tests/dialects.rst
	$(alectryon) --latex-dialect=lualatex -o $@ $<
tests_targets += _output/tests/dialects.lua.tex

# reST → Coq
_output/tests/directive-options.html: tests/directive-options.rst
	$(alectryon) $<
tests_targets += _output/tests/directive-options.html
# reST → LaTeX
_output/tests/directive-options.xe.tex: tests/directive-options.rst
	$(alectryon) $< --latex-dialect xelatex -o $@
tests_targets += _output/tests/directive-options.xe.tex

# reST → HTML
_output/tests/display-flags.html: tests/display-flags.rst
	$(alectryon) $<
tests_targets += _output/tests/display-flags.html

# reST + assertions
_output/tests/docinfo_flags.txt: tests/docinfo_flags.rst
	$(alectryon) $< -o - >/dev/null; echo "exit: $$?" > $@
tests_targets += _output/tests/docinfo_flags.txt

# Run doctests
_output/tests/doctests.out: tests/doctests.py | _output/tests/
	$(PYTHON) $< | sed 's/\(tests\) in [0-9.]\+s$$/\1/g' > $@
tests_targets += _output/tests/doctests.out

# Errors and warnings
_output/tests/errors.py.out: tests/errors.py | _output/tests/
	$(PYTHON) $< | sed 's/\(tests\?\) in [0-9.]\+s$$/\1/g' > $@
tests_targets += _output/tests/errors.py.out

# reST → JSON errors
_output/tests/errors.lint.json: tests/errors.rst
	$(alectryon) $< --backend lint; echo "exit: $$?" >> $@
tests_targets += _output/tests/errors.lint.json
# reST → HTML + errors
_output/tests/errors.txt: tests/errors.rst
	$(alectryon) $< --copy-assets none --backend webpage -o /dev/null 2> $@; echo "exit: $$?" >> $@
tests_targets += _output/tests/errors.txt

# Errors and warnings
_output/tests/errors.sh.out: tests/errors.sh
	PYTHON="$(PYTHON) " ALECTRYON="$(alectryon) " bash $< 2>&1 | sed '/^usage\|^ \{10,\}/d' > $@
tests_targets += _output/tests/errors.sh.out

# Plain Coq → HTML + errors
_output/tests/excepthook.v.out: tests/excepthook.v
	$(alectryon) not_found.v --frontend coq --traceback -o - 2>&1 | sed 's/File ".\+\?", line [0-9]\+/File …, line …/g' | sed '/^    /d' | sed '/^ *$$/d' | uniq | cat > $@; ! test $$? -eq 0
tests_targets += _output/tests/excepthook.v.out

# Plain Coq → HTML + errors
_output/tests/fatal.v.out: tests/fatal.v
	$(alectryon) $< --frontend coq -o - > /dev/null 2> $@; echo "exit: $$?" >> $@
tests_targets += _output/tests/fatal.v.out

# Plain Coq → HTML + errors
_output/tests/fatal_transform.v.out: tests/fatal_transform.v
	$(alectryon) $< --frontend coq -o - > /dev/null 2> $@; echo "exit: $$?" >> $@
tests_targets += _output/tests/fatal_transform.v.out

# Frontend warnings
_output/tests/frontend_warnings.json.out: tests/frontend_warnings.json
	$(alectryon) $< -o - > $@ 2>&1
tests_targets += _output/tests/frontend_warnings.json.out

# Coq+reST → LaTeX
_output/tests/latex_formatting.tex: tests/latex_formatting.v
	$(alectryon) $< --backend latex
tests_targets += _output/tests/latex_formatting.tex

# ReST → HTML
_output/tests/lean3_error.out: tests/lean3_error.rst
	$(alectryon) $< --backend webpage -o /dev/null 2>&1 | sed 's/^\( *\).*\?\([.]lean:\)/\1...\2/g' > $@; echo "exit: $$?" >> $@
tests_targets += _output/tests/lean3_error.out

# Lean → HTML
_output/tests/lists.lean.html: tests/lists.lean
	$(alectryon) $< -o $@
tests_targets += _output/tests/lists.lean.html

# reST → Coq
_output/tests/literate.v: tests/literate.rst
	$(alectryon) $< --backend coq
tests_targets += _output/tests/literate.v

# Coq → reST
_output/tests/literate.v.rst: tests/literate.v
	$(alectryon) $< --backend rst --mark-point 908 ⊙
tests_targets += _output/tests/literate.v.rst
# Coq → reST
_output/tests/literate.marked-end.rst: tests/literate.v
	$(alectryon) $< --backend rst -o - --mark-point 42000 "F"IN | nl | grep "F"IN > $@
tests_targets += _output/tests/literate.marked-end.rst
# Coq → reST
_output/tests/literate.marked-empty.rst: tests/literate.v
	$(alectryon) --frontend coq --backend rst /dev/null -o - --mark-point 42000 "F"IN | nl | grep "F"IN > $@
tests_targets += _output/tests/literate.marked-empty.rst

# Plain Coq → HTML (minified)
_output/tests/minification.v.html: tests/minification.v
	$(alectryon) --frontend coq --html-minification $<
tests_targets += _output/tests/minification.v.html

# reST → HTML
_output/tests/misc.html: tests/misc.rst
	$(alectryon) $<
tests_targets += _output/tests/misc.html

# Coq → HTML
_output/tests/plain_cli.noext.html: tests/plain_cli.rst | _output/tests/
	$(PYTHON) -m "alectryon" --no-header --copy-assets none --frontend coq --backend webpage <(echo "Check nat.") -o - > $@
tests_targets += _output/tests/plain_cli.noext.html
# Coq → HTML
_output/tests/plain_cli.tmp.html: tests/plain_cli.rst | _output/tests/
	TMP=$$(mktemp); \
     $(PYTHON) -m "alectryon" --no-header --copy-assets none --frontend coq --backend webpage $$TMP && cp $$TMP $@
tests_targets += _output/tests/plain_cli.tmp.html
# Coq → HTML
_output/tests/plain_cli.stdin.html: tests/plain_cli.rst | _output/tests/
	echo "Check nat." | $(PYTHON) -m "alectryon" --no-header --copy-assets none --frontend coq --backend webpage - > $@
tests_targets += _output/tests/plain_cli.stdin.html

# reST+* → HTML
_output/tests/polyglot.html: tests/polyglot.rst
	$(alectryon) $<
tests_targets += _output/tests/polyglot.html

# Coq → JSON
_output/tests/recording.v.io.json: tests/recording.v
	$(alectryon) $< --frontend coq --backend json
tests_targets += _output/tests/recording.v.io.json

# IO → HTML
_output/tests/recording.v.html: tests/recording.v.io.json
	$(alectryon) $<
tests_targets += _output/tests/recording.v.html
# IO → HTML
_output/tests/recording.snippets.html: tests/recording.v.io.json
	$(alectryon) $< --backend snippets-html
tests_targets += _output/tests/recording.snippets.html
# IO → LaTeX
_output/tests/recording.snippets.tex: tests/recording.v.io.json
	$(alectryon) $< --backend snippets-latex
tests_targets += _output/tests/recording.snippets.tex

# Coq → HTML
_output/tests/screenshot.html: tests/screenshot.v
	$(alectryon) $<
tests_targets += _output/tests/screenshot.html

# reST → HTML
_output/tests/stylesheets.html: tests/stylesheets.v
	DOCUTILSCONFIG=tests/stylesheets.docutils.conf \
       $(alectryon) $< --pygments-style emacs -o - | sed -r '/^ *<style type="text.css">/,/^ *<.style>/ { /^ *<style |<.style>|Alectryon/b; d}' > $@
tests_targets += _output/tests/stylesheets.html
# reST → LaTeX
_output/tests/stylesheets.part.tex: tests/stylesheets.v
	DOCUTILSCONFIG=tests/stylesheets.docutils.conf \
       $(alectryon) $< --pygments-style emacs --backend latex -o - | sed -r '/^% embedded stylesheet/,/^\\makeatother/ { /^\\makeat|Alectryon/b; d}' > $@
tests_targets += _output/tests/stylesheets.part.tex

# Coq → HTML
_output/tests/syntax_highlighting.html: tests/syntax_highlighting.v
	$(alectryon) $<
tests_targets += _output/tests/syntax_highlighting.html

# Unit tests
_output/tests/unit.py.out: tests/unit.py | _output/tests/
	$(PYTHON) $< | sed 's/\(tests\?\) in [0-9.]\+s$$/\1/g' > $@
tests_targets += _output/tests/unit.py.out

# Coq → reST
_output/tests/unterminated.rst.out: tests/unterminated.rst
	$(alectryon) $< --coq-driver sertop_noexec > $@ 2>&1; echo "exit: $$?" >> $@
tests_targets += _output/tests/unterminated.rst.out

# Coq → reST
_output/tests/unterminated.v.out: tests/unterminated.v
	$(alectryon) $< --backend rst > $@ 2>&1;\
        echo "exit: $$?" >> $@
tests_targets += _output/tests/unterminated.v.out

$(tests_targets): out_dir := _output/tests
targets += $(tests_targets)
