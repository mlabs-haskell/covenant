# Contributing to Covenant

Thank you for your interest in contributing to Covenant! We value, and welcome,
all contributions, whether you are a downstream user of Covenant, or just
interested in the project and using it to develop your skills or do something
fun or interesting.

To ensure that the codebase remains free of error, easy to understand, and
consistent, the Covenant project has a set of practices and requirements for
contributions. To make the process of contributing as easy as possible for both
you and for us, the maintainers, please read and become familiar with these
before contributing.

# Where to start

If you are looking for an easy task for first contributors, we encourage you to
check the ['good first
issue'](https://github.com/mlabs-haskell/covenant/issues?q=is%3Aissue%20state%3Aopen%20label%3A%22good%20first%20issue%22)
label, which will contain tasks that are good for a newcomer to get familiar
with the codebase of Covenant. 

# Project standards

The standards required for the Covenant project as a whole are described in
`STANDARDS.md`. This document may periodically be updated, so check the
changelog section periodically in case something has changed. Some, but not all,
of the standards are enforced by our CI; for all the ones which aren't, ensure
your contribution follows them. Doing so will speed up the contribution process.

# Branch and PR practice

If you are addressing a specific issue, name your branch with your name,
followed by a slash, followed by the issue number (for example, `koz/234`). If
your branch is not addressing a specific issue, name the branch whatever you
want, as long as it's easy to identify.

Normally, PRs should be made directly to `main`. Please tag one of the code
owners (listed in the `CODEOWNERS` file) on your PR to ensure speedy review. We
require at least one acceptance from a reviewer before merging.

# Hard lines

PRs concerning any of the following will _not_ be accepted. Please save both
yourself and us effort by not submitting these.

* Any attempt to add Nix support (of any kind), as well as anything similar
  (such as Guix) to the project. This is a stated non-goal of this project, and
  will remain that way.
* Any direct dependency on Plutus components. We want Covenant to remain a
  standalone component from Plutus, and thus, a dependency on it would violate
  this.
