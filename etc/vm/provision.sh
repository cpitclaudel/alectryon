#!/usr/bin/env bash
## Set up a Vagrant VM for Kôika development
# To set up a non-vagrant VM, run as follows:
# USERNAME=$USER LOGFILE=~/provision.log sudo --preserve-env ./provision.sh

export DEBIAN_FRONTEND=noninteractive
: "${LOGFILE:=/vagrant/provision.log}"
: "${USERNAME=vagrant}"

touch $LOGFILE
chown $USERNAME $LOGFILE
echo "* Starting; see $LOGFILE for details."

echo ""
echo '************************************'
echo '***   Installing base packages   ***'
echo '************************************'

echo '* apt-get update'
apt-get -y update >> $LOGFILE 2>&1
echo '* apt-get install'
apt-get -y install \
		pkg-config make patch unzip git aspcud curl emacs \
		autoconf m4 opam python3 python3-pip
	>> $LOGFILE 2>&1

sudo su $USERNAME <<-EOF
	echo ""
	echo '************************************'
	echo '***   Downloading OPAM packages  ***'
	echo '************************************'

	export OPAMYES=true
	echo '* OPAM init'
	opam init --auto-setup --compiler=4.07.1 >> $LOGFILE 2>&1
	eval \$(opam env)
	echo '* OPAM repo add'
    opam repo add --all-switches coq-released https://coq.inria.fr/opam/released >> $LOGFILE 2>&1
	echo '* OPAM update'
    opam update >> $LOGFILE 2>&1
	echo '* OPAM install (will take a while)'
    opam install coq-serapi=8.10.0+0.7.0 >> $LOGFILE 2>&1

	echo ""
	echo '***********************************'
	echo '*** Downloading Python packages ***'
	echo '***********************************'

	echo '* pip install'
    python3 -m pip install --user pygments==2.5.2 dominate==2.4.0 beautifulsoup4==4.8.2 docutils==0.16
	python3 -m pip install --user numpy scipy matplotlib

	echo ""
	echo '************************************'
	echo '***   Setting up Proof General   ***'
	echo '************************************'

	mkdir -p ~/.emacs.d/
	cat > ~/.emacs.d/init.el <<-EOS
		(require 'package)
		(add-to-list 'package-archives '("melpa" . "https://melpa.org/packages/"))
		(package-initialize)

		;; Basic usability
		(xterm-mouse-mode)
		(load-theme 'tango-dark t)

		;; Alectryon
		(require 'alectryon "~/alectryon-sle2020/src/etc/elisp/alectryon.el")
	EOS

	echo '* package install'
	emacs --batch --load ~/.emacs.d/init.el \
		--eval "(package-refresh-contents)" \
		--eval "(package-install 'flycheck)" \
		--eval "(package-install 'proof-general)" \
		>> $LOGFILE 2>&1

	echo ""
	echo '************************************'
	echo '***       Completing setup       ***'
	echo '************************************'

	echo '* PATH adjustment'
	mkdir -p ~/.bin
	echo 'export PATH="$HOME/.bin:$PATH"' >> ~/.profile

	echo '* Alectryon clone'
	mkdir ~/alectryon-sle2020
	cd ~/alectryon-sle2020
	git clone https://github.com/alectryon-paper/alectryon-paper.github.io.git ae
	git clone https://github.com/cpitclaudel/alectryon --branch sle2020 src
	ln -s ~/alectryon-sle2020/src/alectryon.py ~/.bin/alectryon

	echo ""
	echo '************************************'
	echo '***        Setup complete        ***'
	echo '************************************'

	echo ""
	echo Log into the VM using ‘vagrant ssh’.
EOF

# Local Variables:
# indent-tabs-mode: t
# End:
