# Changelog for `covenant`

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## UNRELEASED

* Expose unsafe constructors `UnsafeMkId` and `UnsafeMkArg` for `Id` and `Arg`
  respectively from `Covenant.Test`
* Add read-only synonyms `Id` and `Arg` for the two data types with the same
  name in `Covenant.ASG`
* Modify `App` to contain the calculated fully-concrete function type of the fn being applied

## 1.3.0 -- 2025-10-07

* Zipper for the ASG in `Covenant.Zipper`
* `topLevelId` function in `Covenant.ASG`
* Changed type name representation of base functors from a `_F` suffix to a `#` prefix. For example, the base functor for `List` is now named `#List` instead of `List_F`. 
* Changed base functor lookup machinery / representation to not require raw TyName text manipulation 
* Provided helper function for safe construction of base functor names from the parent TyName
* `ASG` now exposes a read-only pattern synonym
* `ValNodeInfo`'s pattern for `App` now exposes type applications as well
* JSON serialization and deserialization support for `ASG`s with type
  declarations
* Removed `CaseData` and `CaseList`, as Plutus Core no longer supports them

## 1.2.0 -- 2025-08-27

* Helper function for safely retrieving an in-scope type variable when constructing the ASG  
* Removed Return nodes, associated pattern synonyms, and the `ret` ASGBuilder function
* Reworked the renamer to be context sensitive
* Added new error types for un-renaming
* Modified ASG helper functions and updated tests to conform with renamer rework
* Added support for introduction forms (ValNode stuff, ASG helper function, tests)
* Added support for catamorphism elimination forms
* Added support for pattern matching elimination form

## 1.1.0 -- 2025-07-11

### Added 

* Representation of datatype declarations and datatype types 
* Generators for various flavors of data declaration and value type 
* A "kind checker" which serves as a basic sanity check on datatype declarations ingested by the pipeline 
* Base functor transformation machinery 
* Tests for the base functor transformation 
* Misc internal helpers to support the above functionality 
* Ledger type definitions for use in the ASG
* Support for primops over data types
* Support for arity-six primops in the ASG

Initial version

## 1.0.0 -- 2025-05-07
  
