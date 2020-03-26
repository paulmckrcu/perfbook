% SPDX-License-Identifier: GPL-2.0-or-later
% This file is pfbook.cls
% book class customized for perfbook
% Copyright (C) 2018 Akira Yokosawa
\NeedsTeXFormat{LaTeX2e}[1995/12/01]
\ProvidesClass{pfbook}
              [2020/03/26 v1.4i-ay
 book class customized for perfbook]
%
\DeclareOption*{\PassOptionsToClass{\CurrentOption}{book}}
\ProcessOptions\relax
\LoadClass{book}
% (by Akira Yokosawa)
% Fix indentation behavior of first paragraph in a chapter when twocolumn
% option is specified.
\def\@chapter[#1]#2{\ifnum \c@secnumdepth >\m@ne
                       \if@mainmatter
                         \refstepcounter{chapter}%
                         \typeout{\@chapapp\space\thechapter.}%
                         \addcontentsline{toc}{chapter}%
                                   {\protect\numberline{\thechapter}#1}%
                       \else
                         \addcontentsline{toc}{chapter}{#1}%
                       \fi
                    \else
                      \addcontentsline{toc}{chapter}{#1}%
                    \fi
                    \chaptermark{#1}%
                    \addtocontents{lof}{\protect\addvspace{10\p@}}%
                    \addtocontents{lot}{\protect\addvspace{10\p@}}%
                    \if@twocolumn
                      \@topnewpage[\@makechapterhead{#2}]%
                    \else
                      \@makechapterhead{#2}%
                    \fi
                    \@afterheading}
\def\@schapter#1{\if@twocolumn
                   \@topnewpage[\@makeschapterhead{#1}]%
                 \else
                   \@makeschapterhead{#1}%
                 \fi
                 \@afterheading}
