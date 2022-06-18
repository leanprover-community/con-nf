#!/bin/bash -e

# install elan
set -o pipefail
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- --default-toolchain none -y
~/.elan/bin/lean --version
echo "$HOME/.elan/bin" >> $GITHUB_PATH

# lean deps
pip install mathlibtools

# blueprint deps
sudo apt-get update
sudo apt install graphviz libgraphviz-dev pandoc texlive-full texlive-xetex
pip install invoke
git clone https://github.com/plastex/plastex.git
pip install ./plastex
git clone https://github.com/PatrickMassot/leanblueprint.git
pip install ./leanblueprint
