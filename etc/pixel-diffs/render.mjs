#!/usr/bin/env node
// Usage: render.mjs <inputDir> <outputDir>
// Renders every .html (as .plain.png + .toggled.png) and .pdf (as .png) file
// under <inputDir> to <outputDir>, preserving relative paths.
// HTML is rendered via Playwright; PDF directly via pdfjs-dist in Node.

import { chromium } from 'playwright';
import { mkdir, readFile, readdir, writeFile } from 'node:fs/promises';
import { cpus } from 'node:os';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { getDocument } from 'pdfjs-dist/legacy/build/pdf.mjs';

const [, , inDir, outDir] = process.argv;
if (!inDir || !outDir) {
    console.error('Usage: render.mjs <inputDir> <outputDir>');
    process.exit(2);
}

const scriptDir = path.dirname(fileURLToPath(import.meta.url));
const concurrency = +process.env.PIXEL_DIFF_CONCURRENCY || Math.min(cpus().length, 8);
const PDF_SCALE = 1.5;
const PDF_MARGIN = 16;

async function renderPdf(pdfPath, outPath) {
    const data = new Uint8Array(await readFile(pdfPath));
    const doc = await getDocument({
        data,
        cMapUrl: path.join(scriptDir, 'node_modules/pdfjs-dist/cmaps/'),
        cMapPacked: true,
        standardFontDataUrl: path.join(scriptDir, 'node_modules/pdfjs-dist/standard_fonts/'),
    }).promise;
    const pages = [];
    let maxW = 0, totalH = PDF_MARGIN;
    for (let i = 1; i <= doc.numPages; i++) {
        const page = await doc.getPage(i);
        const viewport = page.getViewport({ scale: PDF_SCALE });
        const { canvas, context } = doc.canvasFactory.create(viewport.width, viewport.height);
        await page.render({ canvasContext: context, viewport }).promise;
        pages.push(canvas);
        maxW = Math.max(maxW, viewport.width);
        totalH += viewport.height + PDF_MARGIN;
        page.cleanup();
    }
    const full = doc.canvasFactory.create(maxW + 2 * PDF_MARGIN, totalH);
    const ctx = full.context;
    ctx.fillStyle = 'white';
    ctx.fillRect(0, 0, full.canvas.width, full.canvas.height);
    let y = PDF_MARGIN;
    for (const c of pages) {
        ctx.drawImage(c, (maxW - c.width) / 2 + PDF_MARGIN, y);
        y += c.height + PDF_MARGIN;
    }
    await writeFile(outPath, full.canvas.toBuffer('image/png'));
    await doc.cleanup();
}

async function waitReady(page) {
    await page.evaluate(() => document.fonts.ready);
    await page.evaluate(async () => { window.MathJax && await MathJax.startup.promise; });
}

// Use playwright's internal expectScreenshot: takes repeated screenshots until
// two consecutive ones are identical. Same logic as `expect().toHaveScreenshot()`
// but callable outside the test runner.
async function stableScreenshot(page, outPath) {
    const { actual } = await page._expectScreenshot({
        screenshotOptions: { fullPage: true },
        isNot: false,
        timeout: 30000,
    });
    await writeFile(outPath, actual);
}

async function renderHtmlVariants(page, htmlPath, rel) {
    await page.goto(pathToFileURL(htmlPath).href, { waitUntil: 'networkidle' });
    await waitReady(page);
    const plainPath = path.join(outDir, rel + '.plain.png');
    await mkdir(path.dirname(plainPath), { recursive: true });
    await stableScreenshot(page, plainPath);
    await page.evaluate(() => {
        document.querySelectorAll('input[type="checkbox"]').forEach(e => { e.checked = !e.checked; });
        // Force layout so any newly-revealed text triggers its font loads
        // before we await document.fonts.ready (which otherwise resolves to
        // the pre-toggle state if nothing is pending yet).
        void document.body.offsetHeight;
    });
    await waitReady(page);
    await stableScreenshot(page, path.join(outDir, rel + '.toggled.png'));
}

const files = (await readdir(inDir, { withFileTypes: true, recursive: true }))
    .filter(e => e.isFile() && (e.name.endsWith('.html') || e.name.endsWith('.pdf')))
    .map(e => path.relative(inDir, path.join(e.parentPath, e.name)))
    .sort();

await mkdir(outDir, { recursive: true });

const browser = await chromium.launch({ args: [
    '--font-render-hinting=none',
    '--disable-lcd-text',
    '--disable-font-subpixel-positioning',
    '--force-color-profile=srgb',
    '--disable-partial-raster',
    '--disable-skia-runtime-opts',
    '--force-device-scale-factor=1',
]});
const context = await browser.newContext({ viewport: { width: 1024, height: 768 } });

const iter = files[Symbol.iterator]();
const workers = Array.from({ length: concurrency }, async () => {
    for (const rel of iter) {
        try {
            const srcPath = path.join(inDir, rel);
            if (rel.endsWith('.pdf')) {
                const outPath = path.join(outDir, rel + '.png');
                await mkdir(path.dirname(outPath), { recursive: true });
                await renderPdf(srcPath, outPath);
            } else {
                const page = await context.newPage();
                try { await renderHtmlVariants(page, srcPath, rel); }
                finally { await page.close(); }
            }
            console.log(rel);
        } catch (e) { console.error(`FAIL ${rel}: ${e.message}`); process.exitCode = 1; }
    }
});

await Promise.all(workers);
await context.close();
await browser.close();
