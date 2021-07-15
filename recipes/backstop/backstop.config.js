const fs = require("fs");
const path = require('path');

function scenarios(dir) {
    return (fs
            .readdirSync(dir)
            .filter(f => f.match(/.*[.]html$/g))
            .flatMap(f => ['plain', 'toggled'].map(style => ({
                "label": `${f}_${style}`,
                "alectryon_style": style,
                "url": "file://" + path.resolve(dir, f),
                // "referenceUrl": "",
                "readyEvent": "",
                // "readySelector": "",
                "delay": 20,
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
            }))));
}

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
    "scenarios": scenarios("../output/"),
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
    "asyncCaptureLimit": 5,
    "asyncCompareLimit": 50,
    "debug": false,
    "debugWindow": false
}
