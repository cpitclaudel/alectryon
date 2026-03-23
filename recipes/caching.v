(*|
======================================
 Caching results for faster execution
======================================

Alectryon can generate cache files to memoize Coq's output, yielding faster compilation when Coq fragments embedded in a document have not changed::

   alectryon --cache-directory _output/ --cache-compression=xz caching.v
     # Coq+reST → HTML, cached to _output/caching.v.cache; produces ‘caching.html’

(The ``--cache-compression`` flag is optional; the default is to not compress caches.)

Independently of caching, Alectryon can also record its output as JSON, for later replay or as input to other pipelines::

   alectryon --frontend coq --backend json caching.v
     # Coq → JSON recording; produces ‘caching.v.io.json’

.. coq::
|*)

Print nat.
