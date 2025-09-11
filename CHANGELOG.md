# Changelog for `covenant`

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## Unreleased 

* Changed type name representation of base functors from a `_F` suffix to a `#` prefix. For example, the base functor for `List` is now named `#List` instead of `List_F`. 

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
  
