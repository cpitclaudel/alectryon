MathJax = {
    options: {
        processHtmlClass: 'alectryon-io'
    },
    startup: {
        pageReady: function () {
            document.querySelectorAll(".coq-math .highlight")
                .forEach(function (e) { // Wrap each math node in math delimiters
                    e.innerHTML = e.innerHTML.replace(/([\\]mathbb{N})/g, '\\($1\\)');
                });
            // Then run MathJax
            return MathJax.startup.defaultPageReady();
        }
    }
};
