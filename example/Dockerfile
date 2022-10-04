# BUILD
## docker build -t customeverparse:everparse .

# START AND RUN
## docker run --rm -v $PWD:/pwd -d --name customeverparse -i customeverparse:everparse && docker exec -it customeverparse /bin/bash


FROM projecteverest/everest-linux

USER root

RUN ln -s /home/test/everparse/bin/qd.exe /bin/quackyducky 
RUN ln -s /home/test/everparse/bin/3d.exe /bin/3d 
RUN ln -s /home/test/karamel/krml /bin/krml 
RUN ln -s /home/test/FStar/bin/fstar.exe /bin/fstar 

USER test

ENV FSTAR_HOME="/home/test/FStar"
ENV KRML_HOME="/home/test/karamel"
ENV EVERPARSE_HOME="/home/test/everparse"
ENV LOWPARSE_HOME="${EVERPARSE_HOME}/src/lowparse"
