ARG rel=latest
FROM ubuntu:$rel

RUN apt-get update && apt-get upgrade -y && apt-get install -y locales && \
    localedef -i en_US -c -f UTF-8 -A /usr/share/locale/locale.alias en_US.UTF-8 && \
    rm -rf /var/lib/apt/lists/*
ENV LANG en_US.utf8
RUN apt-get update && DEBIAN_FRONTEND=noninteractive TZ=UTC apt-get install -y tzdata && \
    rm -rf /var/lib/apt/lists/*
RUN apt-get update && apt-get install -y fig2ps inkscape xfig graphviz psutils \
    texlive-publishers texlive-pstricks texlive-science texlive-fonts-extra \
    make nano vim git curl gnuplot-nox time poppler-utils librsvg2-bin && \
    rm -rf /var/lib/apt/lists/*
COPY steel-city-comic.regular.ttf /usr/local/share/fonts/
RUN fc-cache /usr/local/share/fonts/
WORKDIR /opt
RUN curl https://gitlab.com/latexpand/latexpand/-/archive/v1.3/latexpand-v1.3.tar.gz -o - | tar xfz - && \
    sed -i -e 's/@LATEXPAND_VERSION@/v1.3/' latexpand-*/latexpand && \
    cp latexpand-*/latexpand /usr/local/bin
ARG uid=0
ARG gid=0
ARG user=perfbook
ARG group=perfbook
RUN if [ $uid -ne 0 ] ; then \
    groupadd -g $gid $group ; \
    useradd -u $uid -g $gid -m $user ; \
    fi
VOLUME /work
USER $uid:$gid
WORKDIR /work
CMD /bin/bash
