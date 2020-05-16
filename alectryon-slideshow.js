var Alectryon;
(function(Alectryon) {
    var slideshow;
    (function (slideshow) {
        function anchor(sentence) { return "#" + sentence.id; }

        function current_sentence() { return slideshow.sentences[slideshow.pos]; }

        function unhighlight(sentence) {
            if (sentence) sentence.classList.remove("alectryon-target");
        }

        function highlight(sentence) {
            sentence.classList.add("alectryon-target");
        }

        function navigate(pos) {
            unhighlight(current_sentence());
            slideshow.pos = Math.min(Math.max(pos, 0), slideshow.sentences.length - 1);
            highlight(current_sentence());
        }

        function init() {
            slideshow.pos = -1;
            slideshow.sentences = document.getElementsByClassName("coq-sentence");
        }

        slideshow.next = function() { navigate(slideshow.pos + 1); };
        slideshow.previous = function() { navigate(slideshow.pos + -1); };
        window.addEventListener('DOMContentLoaded', init);
    })(Alectryon.slideshow || (Alectryon.slideshow = {}));
})(Alectryon || (Alectryon = {}));
