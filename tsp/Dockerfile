FROM zsol/haskell-platform-2014.2.0.0

MAINTAINER Shou Ya <shouyatf@gmail.com>


USER root
WORKDIR /

RUN sed -i 's/archive.ubuntu.com/mirrors.aliyun.com/g' /etc/apt/sources.list

RUN apt-get update
RUN cabal update

RUN apt-get install -y libcairo2-dev
# RUN cabal install gtk2hs-buildtools
RUN cabal install gloss

ENV DISPLAY=:0

USER haskell
ADD TSPGraph.hs /

CMD runghc TSPGraph.hs
