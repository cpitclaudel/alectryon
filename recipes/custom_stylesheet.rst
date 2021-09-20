==============================================
 Using a custom CSS stylesheet with Alectryon
==============================================

There are multiple ways to add custom stylesheets to an Alectryon document:

1. Use a ``.. raw:: html`` block::

      .. raw:: html

         <link rel="stylesheet" href="custom.css" />

2. Use a custom Alectryon driver and modify ``alectyron.html.ASSETS.DOCUTILS_CSS``::

      alectryon.html.ASSETS.DOCUTILS_CSS += ("custom.css",)

3. If using Sphinx, add your stylesheet in ``conf.py``::

      html_css_files = ['css/custom.css']

4. If using plain Docutils, use the ``stylesheet`` option::

      [html writers]
      stylesheet=custom.css

   As of this writing, the ``stylesheet_path`` option does not work with Alectryon.

To compile this file using the last option:

   $ DOCUTILSCONFIG=custom_stylesheet.docutils.conf alectryon \
     custom_stylesheet.rst
       # Coq+reST → HTML; produces ‘custom_stylesheet.html’
