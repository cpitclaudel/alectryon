#!/usr/bin/env node
// Usage: screenshot.mjs <src.html> <dst.pdf>
// Renders an alectryon HTML file to a landscape PDF, for use as a project illustration.

import { chromium } from 'playwright';
import path from 'node:path';
import { pathToFileURL } from 'node:url';

const [, , src, dst] = process.argv;
if (!src || !dst) {
    console.error('Usage: screenshot.mjs <src.html> <dst.pdf>');
    process.exit(2);
}

const browser = await chromium.launch();
const page = await browser.newPage();
await page.emulateMedia({ media: 'screen' });
await page.goto(pathToFileURL(path.resolve(src)).href, { waitUntil: 'networkidle' });

await page.addStyleTag({ content: `
    body { font-size: 26px; }
    pre.alectryon-io { font-family: Iosevka; margin-top: 0.5em; }
    .alectryon-banner { display: none; }
    .big p { font-size: 87.5% }
    .big .alectryon-input { font-size: 125%; }
    p { print-color-adjust: exact; }
`});
await page.evaluate(() => {
    document.querySelector('.alectryon-root').classList.add('alectryon-windowed');
    document.querySelectorAll('.alectryon-extra-goal-toggle').forEach(c => { c.checked = true; });
    document.querySelectorAll('.alectryon-sentence').forEach(s => {
        if (s.innerText.match(/destruct y/)) s.classList.add('alectryon-target');
    });
});
await page.evaluate(() => document.fonts.ready);
await page.evaluate(async () => { window.MathJax && await MathJax.startup.promise; });

await page.pdf({
    path: path.resolve(dst),
    printBackground: true,
    width: `${838 * 1.85}px`,
    height: '855px',
});
await browser.close();
