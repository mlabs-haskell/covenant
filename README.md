# Covenant

# What is this?

Covenant is a standalone IR, designed as a target for front-end DSLs for writing
Cardano scripts. It uses [call-by-push-value][cbpv] and is
[Turner-total][turner-total], which gives it a high degree of analyzability.
Furthermore, it uses a fully hash-consed structure.

# How do I use this?

This is currently a work-in-progress. Begin with the documentation in
`Covenant.ASG` and `Covenant.Type`.

# What do I need?

Our policy is to support the latest three GHC versions; see the Cabal file's
`tested-with` field to see which exact versions are supported. This is enforced
using `get-tested` in our CI.

We support only [Tier 1 platforms](https://gitlab.haskell.org/ghc/ghc/-/wikis/platforms#tier-1-platforms). 
Covenant is developed using the lowest supported version.

# License

Covenant is licensed under Apache 2.0. Please see the `LICENSE` file for more
information. 

# References

* [Catalyst proposal for
  Covenant](https://projectcatalyst.io/funds/13/f13-cardano-open-developers/mlabs-static-analysis-with-covenant)

[cbpv]: https://www.cs.bham.ac.uk/~pbl/papers/thesisqmwphd.pdf
[turner-total]: https://www.jucs.org/jucs_10_7/total_functional_programming/jucs_10_07_0751_0768_turner.pdf
