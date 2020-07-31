FROM coqorg/coq:8.4.6

RUN sudo apt-get update && sudo apt-get install -y vim

RUN opam install -y coq-mathcomp-algebra.1.6.1

RUN opam install -y menhir.20171222

RUN git clone --recursive https://github.com/haslab/CircGen.git

RUN (cd CircGen; make clean_setup_build_dir; cd build; ./configure bool-circ-linux; make depend; make)

