Property-based testing slides
=============================

These are my slides for talks given related to Property-based testing.




The [current version of the slides](slides.md) uses
[patat](https://github.com/jaspervdj/patat) and markdown format.


Running
-------

Displaying the slides is a pretty simple

```bash
patat slides.md
```

To install patat, the repository is a cabal package depending on pata,
however the simplest way to get going on ubuntu is a simple

```bash
bash ubuntu_preinstall.sh
cabal install patat
```

After which patat should be in `~/.cabal/bin`. It is recommended to
include that directory in PATH.
