test:
	+$(MAKE) -C recipes clean
	+$(MAKE) -C recipes

lint:
	pylint --rcfile=setup.cfg alectryon
