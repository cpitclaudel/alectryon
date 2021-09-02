===========
 Plain CLI
===========

This file calls Alectryon without the flags that other tests use.  To compile::

   $ python -m "alectryon" --no-header --copy-assets none --frontend coq --backend webpage <(echo "Check nat.") -o - > plain_cli.noext.html
     # Coq → HTML; produces ‘plain_cli.noext.html’

   $ TMP=$(mktemp); \
     python -m "alectryon" --no-header --copy-assets none --frontend coq --backend webpage $TMP && \
       cp $TMP plain_cli.tmp.html
     # Coq → HTML; produces ‘plain_cli.tmp.html’

   $ echo "Check nat." | \
     python -m "alectryon" --no-header --copy-assets none --frontend coq --backend webpage - > plain_cli.stdin.html
     # Coq → HTML; produces ‘plain_cli.stdin.html’
