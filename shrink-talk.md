---
title: Help, I need to download 1gb of data to reproduce the bug!
author: Eivind Jahren
date: 2019

...

Let's go back to 2014...

+++

* Russian forces are on the crimean peninsula
* The Ebola epidemic in West Africa has just begun
* And I am in the midst of figuring out a big bug in my phd thesis.

+++

* My SAT solver is producing the wrong result.
* Can compare result with someone elses SAT solver.
* 10mb input file
* Takes about 2 minutes and more than 100,000 inference steps.

---

I try several approaches

+++

valgrind

+++

conditional breaks in debugger

+++

staring contest with the code


+++

Finally: finding a smaller input file

+++

The data: $ (x1 \lor \lnot x2 \lor x3) \land (x4 \ldots $

+++

Really just sets of sets of numbers

+++

Use "shrinking": steepest gradiant descent search


---

Shrinking was developed for Property Testing

+++

QuickCheck: a haskell property testing library

+++

Hypothesis: a python property testing library

+++

With Hypothesis and QuickCheck, no need to write the shrinking algorithm...

+++

... But we will do that anyways

