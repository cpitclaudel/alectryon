module.exports = async (page, scenario, vp) => {
    console.log('SCENARIO > ' + scenario.label);
    await require('./clickAndHoverHelper')(page, scenario);

    // Toggle checkboxes
    switch (scenario.alectryon_style) {
    case 'plain': break;
    case 'toggled':
        await page.evaluate(async () => {
            document.querySelectorAll('input[type="checkbox"]').forEach(e => {
                e.checked = !e.checked;
            });
        });
        break;
    }

    // Wait for fonts
    await page.evaluateHandle('document.fonts.ready');

    // Wait for MathJax
    await page.evaluate(async () => {
        window.MathJax && await MathJax.startup.promise;
    });
};
