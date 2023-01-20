FROM texlive/texlive:latest

# Install Python 3.10
WORKDIR /py
RUN apt update && apt install -y build-essential zlib1g-dev libncurses5-dev \
  libgdbm-dev libnss3-dev libssl-dev libreadline-dev libffi-dev \
  libsqlite3-dev wget libbz2-dev liblzma-dev
RUN apt upgrade -y
RUN wget https://www.python.org/ftp/python/3.10.0/Python-3.10.0.tgz
RUN tar -xf Python-3.10.*.tgz
WORKDIR /py/Python-3.10.0
RUN ./configure
RUN make
RUN make altinstall
WORKDIR /

# Install blueprint dependencies
RUN python3.10 -m pip install mathlibtools invoke
RUN apt install graphviz libgraphviz-dev pandoc -y
RUN git clone https://github.com/plastex/plastex.git
RUN python3.10 -m pip install ./plastex
RUN rm -rf ./plastex
RUN git clone https://github.com/PatrickMassot/leanblueprint.git
RUN python3.10 -m pip install ./leanblueprint
RUN rm -rf ./leanblueprint

# Install doc-gen
RUN git clone https://github.com/leanprover-community/doc-gen.git
RUN python3.10 -m pip install -r ./doc-gen/requirements.txt
RUN rm -rf ./doc-gen

# Install lean
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf \
  | sh -s -- --default-toolchain none -y

WORKDIR /src

# Run the continuous integration pipeline
ENTRYPOINT inv ci
