MathJax = {
    options: {
        processHtmlClass: 'mathjax_process|alectryon-io'
    },
    startup: {
        pageReady: function () {
            document.querySelectorAll( // Find blocks to replace math in
                ".coq-math .alectryon-input, " +
                ".coq-math .alectryon-message, " +
                ".coq-math .goal-conclusion, " +
                ".coq-math .hyp-body span, " +
                ".coq-math .hyp-type span"
            ).forEach(function (e) { // Wrap each math node in math delimiters
                e.innerHTML = e.innerHTML.replace(/([\\]mathbb{N})/g, '\\($1\\)');
            });
            // Then run MathJax
            return MathJax.startup.defaultPageReady();
        }
    }
};
