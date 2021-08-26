const fs = require("fs");
const path = require('path');

function* recSync(dir, root = null) {
    root = root || dir;
    for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
        const pth = path.resolve(dir, entry.name);
        if (entry.isDirectory())
            yield* recSync(pth);
        else
            yield { name: entry.name,
                    path: pth };
    }
}

function scenarios(dir) {
    const shared_props = {
        // "referenceUrl": "",
        "readyEvent": "",
        // "readySelector": "",
        "delay": 0,
        // "hideSelectors": [],
        // "removeSelectors": [],
        // "hoverSelector": "",
        // "clickSelector": "",
        // "postInteractionWait": 0,
        // "selectors": [],
        // "selectorExpansion": true,
        "expect": 0,
        "misMatchThreshold" : 0,
        "requireSameDimensions": true
    };

    const files = [...recSync(dir)];

    const html = files
          .filter(f => f.name.match(/.*[.]html$/g))
          .flatMap(f => ['plain', 'toggled'].map(style => ({
              "label": `${f.name}_${style}`,
              "url": "file://" + f.path,
              ...shared_props })));

    const pdf = files
          .filter(f => f.name.match(/.*[.]pdf$/g))
          .map(f => ({
              "label": `${f.name}_pdf`,
              "url": `http://localhost:1535/recipes/backstop/pdfjs.html#../_output/${path.relative(dir, f.path)}`,
              ...shared_props }));

    return [...html, ...pdf];
}

const dir = process.env.BACKSTOP_DIR || "../_output/";

module.exports = {
    "id": "backstop_default",
    "viewports": [
        {
            "label": "tablet",
            "width": 1024,
            "height": 768
        }
    ],
    "onReadyScript": "puppet/onReady.js",
    "scenarios": scenarios(dir),
    "paths": {
        "bitmaps_reference": "backstop_data/bitmaps_reference",
        "bitmaps_test": "backstop_data/bitmaps_test",
        "engine_scripts": "backstop_data/engine_scripts",
        "html_report": "backstop_data/html_report",
        "ci_report": "backstop_data/ci_report"
    },
    "report": ["browser"],
    "engine": "puppeteer",
    "engineOptions": {
        "args": ["--no-sandbox"]
    },
    "asyncCaptureLimit": 10,
    "asyncCompareLimit": 20,
    "debug": false,
    "debugWindow": false
}
