module.exports = async (page, scenario, vp) => {
    console.log('SCENARIO > ' + scenario.label);
    await require('./clickAndHoverHelper')(page, scenario);

    // Wait for fonts
    await page.evaluateHandle('document.fonts.ready');
    await page.evaluate(async () => {
        if (document.MathJax)
            await MathJax.startup.promise;
    });

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
};
