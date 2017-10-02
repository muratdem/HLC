## Synopsis

This folder shows Pluscal/TLA+ modeling of Hybrid Logical Clocks and Hybrid Vector Clocks.

"hlc.tla" models Hybrid Logical Clocks in PlusCal.
http://muratbuffalo.blogspot.com/2014/07/hybrid-logical-clocks.html

"hlcnaive2.tla" shows a naive implementation of hybrid logical clocks. That naive implementation has a bug, where the logical clock can gradually but unboundedly gets ahead of the physical clock. That counterexample is hard to find and involves 30 steps in the algorithm. That is an example TLA+ modeling proves valuable.

vc.tla models Hybrid Vector Clocks in PlusCal.
http://muratbuffalo.blogspot.com/2015/10/analysis-of-bounds-on-hybrid-vector.html
https://www.cse.buffalo.edu//~demirbas/publications/augmentedTime.pdf

Also see https://github.com/muratdem/PlusCal-examples for more PlusCal examples.
## Installation

To run these Pluscal/TLA+ models, you need the TLA+ toolkit, available at
http://research.microsoft.com/en-us/um/people/lamport/tla/tools.html

## Contributors

@muratdem

## License

MIT license.
