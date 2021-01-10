FROM ubuntu:focal

RUN apt-get update && apt-get install -y locales && \
    localedef -i en_US -c -f UTF-8 -A /usr/share/locale/locale.alias en_US.UTF-8 && \
    rm -rf /var/lib/apt/lists/*
ENV LANG en_US.utf8
RUN apt-get update && DEBIAN_FRONTEND=noninteractive TZ=UTC apt-get install -y tzdata && \
    rm -rf /var/lib/apt/lists/*
RUN apt-get update && apt-get install -y fig2ps inkscape xfig graphviz psutils \
    texlive-publishers texlive-pstricks texlive-science texlive-fonts-extra \
    make nano vim git && \
    rm -rf /var/lib/apt/lists/*
COPY steel-city-comic.regular.ttf /usr/local/share/fonts/
RUN fc-cache /usr/local/share/fonts/
ARG uid=1000
ARG gid=1000
ARG user=perfbook
ARG group=perfbook
RUN groupadd -g $gid $group && useradd -u $uid -g $gid -m $user
VOLUME /work
USER $uid:$gid
WORKDIR /work
CMD /bin/bash
