FROM texlive/texlive:latest

# Install Python 3.9
RUN apt update
RUN apt install software-properties-common -y
RUN apt install --reinstall ca-certificates
RUN apt install dirmngr --install-recommends -y
RUN add-apt-repository ppa:deadsnakes/ppa
RUN apt install python3.9 python3.9-dev python3-pip -y

# Install blueprint dependencies
RUN python3.9 -m pip install mathlibtools invoke
RUN apt install graphviz libgraphviz-dev pandoc -y
RUN git clone https://github.com/plastex/plastex.git
RUN python3.9 -m pip install ./plastex
RUN rm -rf ./plastex
RUN git clone https://github.com/PatrickMassot/leanblueprint.git
RUN python3.9 -m pip install ./leanblueprint
RUN rm -rf ./leanblueprint

# Install lean
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf \
  | sh -s -- --default-toolchain none -y

WORKDIR /src

COPY entrypoint.sh /entrypoint.sh

# Run the continuous integration pipeline
ENTRYPOINT /entrypoint.sh
