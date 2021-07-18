(*|
======================================
 Caching results for faster execution
======================================

Alectryon can generate cache files to memoize Coq's output, yielding faster compilation when Coq fragments embedded in a document have not changed::

   alectryon --cache-directory _output/ --cache-compression=xz caching.v
   # Coq+reST → HTML, cached to _output/caching.v.cache; produces ‘caching.html’

(The ``--cache-compression`` flag is option; the default is to not compress caches.)
|*)

Print nat.
