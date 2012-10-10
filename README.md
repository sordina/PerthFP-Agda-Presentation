Perth Functional Programmers - Agda Presentation
=========================

Source for my Agda Presentation to the <a href="http://www.meetup.com/PerthFP/">Perth Functional Programmers Group</a>

## Overview

* Philosophy
* Syntax
* Basic Types
* Inductive Types
* --- Break ---
* Dependent Types
* Theorems and Proofs
* Conclusion
* --- Questions ---

## Recommended Reading

Agda is an advanced dependently-typed programming-language / theorem-prover. In this
tutorial I will attempt to make my examples self-contained, however, I will
use many constructs found in Haskell as examples.
As such, it is probably a good idea to have a play with some Haskell before
attempting to do anything serious with Agda. A good resource for getting a
feeling for Haskell is <a href="http://learnyouahaskell.com/">Learn You a Haskell for Great Good</a>
which can be read online for free.

An overview of the drive behind Agda can be gleamed from:

* <a href="http://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence">Wikipedia - The Curry-Howard Isomorphism</a>
* <a href="http://en.wikipedia.org/wiki/Intuitionistic_type_theory">Wikipedia - Martin-Löf Type Theory</a>
* <a href="http://www.jonmsterling.com/posts/2012-09-07-pi-is-for-power-sigma-for-product.html">Pi is for Power, Sigma for Product</a>
* <a href="https://github.com/liamoc/learn-you-an-agda">Learn you an Agda for Great Good (incomplete)</a>

There are many resources available online for leaning Agda, unfortunately they are
often extremely academic and found in the form of research-papers and workshop documents.
Some of the best that I have come across so far are:

* <a href="http://www.cse.chalmers.se/~ulfn/darcs/AFP08/LectureNotes/AgdaIntro.pdf">Dependently Typed Programming in Agda</a>
* <a href="http://www.cse.chalmers.se/~ulfn/papers/tphols09/tutorial.pdf">A Brief Overview of Agda – A Functional Language with Dependent Types</a>
* <a href="http://www.cse.chalmers.se/~peterd/papers/DependentTypesAtWork.pdf">Dependent Types at Work</a>
* <a href="http://www.cs.nott.ac.uk/~txa/talks/nijmegen-03.pdf">Why Dependent Types Matter (Epigram)</a>
* <a href="http://www.paultaylor.eu/stable/prot.pdf">Proofs and Types</a>
* <a href="http://www.cse.chalmers.se/research/group/logic/book/book.pdf">Programming in Martin-Löf's Type Theory</a>
* <a href="https://entropia.de/wiki/images/c/cf/AgdaTalk.pdf">Dependent Types in Game Simulation (In German)</a>
* <a href="http://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/fast+loose.pdf">Fast and Loose Reasoning is Morally Correct</a>
* <a href="http://www.andres-loeh.de/PiSigma/PiSigma.pdf">Pi Sigma - Dependent Core</a>


Some of these papers are related to natural-deduction and dependent-types in general, but are still useful.

## Instructions for Installing Agda

* Install Haskell
* Install Agda
* Install Emacs
* Download the Agda Standard Library
* Download Haskell-Mode
* Configure Emacs
* Test configuration

### Install Haskell

Grab the latest Haskell-Platform from http://www.haskell.org/platform/

Check that your install is working:

    ghc   --version
    cabal --version

### Install Agda

    cabal --update
    cabal install agda agda-executable

### Install Emacs

Use your package-manager, or download from http://www.gnu.org/software/emacs/

There may be issues if you use Emacs \>= 24.

    apt-get install emacs


### Download the Agda Standard Library

Get version 0.6 from http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary

Unpack this somewhere stable and note the location of the 'src' folder.

Make sure that

    agda-mode locate

returns a string.

### Download Haskell-Mode

Grab the latest haskell-mode from Github at https://github.com/haskell/haskell-mode

You can download this with git, or just grab the archive from the downloads section.

Unpack this somewhere stable and note the location of the 'haskell-site-file' file.

### Configure Emacs

Ensure that your ~/.emacs contains the following lines (adjust if you know what you're doing):

    (prefer-coding-system       'utf-8)
    (set-default-coding-systems 'utf-8)
    (set-terminal-coding-system 'utf-8)
    (set-keyboard-coding-system 'utf-8)

    (load "~/Library/haskell-mode/haskell-site-file")

    (custom-set-variables '(agda2-include-dirs (quote ("." "/Users/lyndon/Library/Agda/lib/src"))))

    (load-file (let ((coding-system-for-read 'utf-8))
                    (shell-command-to-string "agda-mode locate")))

Make sure that you have replaced the sections

* ~/Library/haskell-mode/haskell-site-file
* /Users/lyndon/Library/Agda/lib/src

with the locations where you extracted Haskell-Mode and the Standard Library.

### Test Configuration

Run:

    emacs test.agda

This should load test.agda in emacs without any errors.

Enter the following code:

    module test where

Hit `C-c C-l`

If the file now has syntax-highlighting, then your setup is working!

If not... Sorry :-(
