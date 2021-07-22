#!/usr/bin/env node

const puppeteer = require('puppeteer');
const path = require('path');

async function screenshot(src, dst, options={}, pdfOptions={}, launchOptions={}) {
    const browser = await puppeteer.launch({
        // executablePath: "google-chrome",
        ...launchOptions
    });

    const page = await browser.newPage();
    page.emulateMediaType('screen');

    await page.evaluateOnNewDocument(function() {
        window.runDelayed = f =>
            (window.delayed = window.delayed || []).push(f);
    });

    // https://github.com/puppeteer/puppeteer/issues/422, but this is not enough
    // when a font isn't used until later (e.g. the bold font of hyp names)
    await page.goto('file://' + src, { waitUntil: 'networkidle2' });

    await page.evaluate(function() {
        const html = document.querySelector("html");
        const link = document.createElement("style");
        // link.rel = "stylesheet";
        link.type = "text/css";
        link.innerText = `
          body { font-size: 26px; /* background: #eeeeec88; */ }
          pre.alectryon-io { font-family: Iosevka; margin-top: 0.5em; }
          .alectryon-banner { display: none; }
          .big p { font-size: 87.5% }
          .big .alectryon-input { font-size: 125%; }
          p { /* https://stackoverflow.com/questions/13975198/ */
            -webkit-print-color-adjust: exact;
            -webkit-filter: blur(0);
          }
        `;
        document.head.appendChild(link);

        document.querySelector('.alectryon-root').classList.add('alectryon-windowed');
        document.querySelectorAll('.alectryon-extra-goal-toggle').forEach(c => c.checked = true);
        document.querySelectorAll(".alectryon-sentence").forEach(s => {
            if (s.innerText.match(/destruct y/))
                s.classList.add('alectryon-target');
        })
    });

    options.script && await page.evaluate(options.script);

    // Make sure that any fonts needed by text revealed by `options.script` are
    // actually loaded.
    await page.evaluateHandle('document.fonts.ready');
    // Make sure that MathJax has rendered
    await page.evaluateHandle(async () => {
        window.MathJax && await MathJax.startup.promise;
    });

    await page.pdf({ path: dst, printBackground: true,
                     width: `${838 * 1.85}px`,
                     height: `855px`,
                     ...pdfOptions });

    await browser.close();
}

async function cli(...args) {
    const fsrc = path.resolve(process.argv[2]);
    const fdst = path.resolve(process.argv[3]);
    await screenshot(fsrc, fdst, ...args);
}

cli();
