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

        function scroll(sentence) {
            // Put the top of the current fragment close to the top of the
            // screen, but scroll it out of view if showing it requires pushing
            // the sentence past half of the screen.  If sentence is already in
            // a reasonable position, don't move.
            var parent = sentence.parentElement;
            while (parent && !parent.classList.contains("alectryon-root"))
                parent = parent.parentElement;

            var rect = function(e) { return e.getBoundingClientRect(); };
            var parent_box = parent ? rect(parent) : { y: 0, height: window.innerHeight },
                sentence_y = rect(sentence).y - parent_box.y,
                fragment_y = rect(sentence.parentElement).y - parent_box.y;

            console.assert(sentence_y >= fragment_y);
            if (sentence_y < 0.1 * parent_box.height ||
                sentence_y > 0.7 * parent_box.height) {
                (parent || window).scrollBy(
                    0, Math.max(sentence_y - 0.5 * parent_box.height,
                                fragment_y - 0.1 * parent_box.height));
            }
        }

        function navigate(pos, inhibitScroll) {
            unhighlight(current_sentence());
            slideshow.pos = Math.min(Math.max(pos, 0), slideshow.sentences.length - 1);
            var sentence = current_sentence();
            highlight(sentence);
            if (!inhibitScroll)
                scroll(sentence);
        }

        function onkeydown(e) {
            e = e || window.event;
            switch(e.keyCode) {
            case 33: // Page up
            case 37: // Arrow left
            case 72: // h
            case 80: // p
                slideshow.previous(); break;
            case 34: // Page down
            case 39: // Arrow right
            case 76: // l
            case 78: // n
                slideshow.next(); break;
            default: return;
            }
            e.preventDefault();
        }

        function start() {
            slideshow.navigate(0);
        }

        function end() {
            unhighlight(current_sentence());
        }

        function handleClick(evt) {
            if (evt.ctrlKey) {
                navigate(evt.currentTarget.alectryon_index, true);
                // document.getSelection().removeAllRanges();
                evt.preventDefault();
            }
        }

        function init() {
            document.onkeydown = onkeydown;
            slideshow.pos = -1;
            slideshow.sentences = Array.from(document.getElementsByClassName("coq-sentence"));
            slideshow.sentences.forEach(function (s, idx) {
                s.addEventListener('click', handleClick, false);
                s.alectryon_index = idx;
            });
        }

        slideshow.start = start;
        slideshow.end = end;
        slideshow.next = function() { navigate(slideshow.pos + 1); };
        slideshow.previous = function() { navigate(slideshow.pos + -1); };
        window.addEventListener('DOMContentLoaded', init);
    })(Alectryon.slideshow || (Alectryon.slideshow = {}));
})(Alectryon || (Alectryon = {}));
