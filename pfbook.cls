% SPDX-License-Identifier: GPL-2.0-or-later
% This file is pfbook.cls
% book class customized for perfbook
% Copyright (C) 2018 Akira Yokosawa
\NeedsTeXFormat{LaTeX2e}[1995/12/01]
\ProvidesClass{pfbook}
              [2018/04/01 v1.4h-pem-ay
 book class customized for perfbook]
% (by Paul E. McKenney)
% Add an option "letterpaperhb" in order to generate 10.75x8.25in pages
% for hardcover books.
\DeclareOption{letterpaperhb}
   {\setlength\paperheight {10.75in}%
    \setlength\paperwidth  {8.25in}}
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
