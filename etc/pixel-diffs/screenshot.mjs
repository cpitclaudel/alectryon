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
await page.evaluate(() => document.fonts.ready);
await page.pdf({
    path: path.resolve(dst),
    printBackground: true,
    width: `${838 * 1.85}px`,
    height: '855px',
});
await browser.close();
