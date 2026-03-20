===========
 Plain CLI
===========

This file calls Alectryon without the flags that other tests use.  To compile::

   $ TMP=$(mktemp --tmpdir alectryon-XXXXX-tmp); echo "Check nat." > $TMP; \
       python -m "alectryon" --no-header --copy-assets none --frontend coq --backend webpage $TMP -o - | \
       sed 's/alectryon-.....-tmp/tmp/g' > plain_cli.noext.html
         # Coq → HTML; produces ‘plain_cli.noext.html’

   $ echo "Check nat." | \
       python -m "alectryon" --no-header --copy-assets none --frontend coq --backend webpage - > plain_cli.stdin.html
         # Coq → HTML; produces ‘plain_cli.stdin.html’
