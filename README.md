HyperOCM is a library for rewriting up to only-connectivity-matters in the Rocq proof assistant. 

# Usage

HyperOCM is still in development, so is not usable at this time. 

# Layout

The three subdirectories containing the development are [src/](src/), [theories/](theories/), and [examples/](examples/). [src/] contains the Rocq plugin which exposes an interface to the Hypercaml graph library from Ltac2, in the file [hypercaml_interface.ml](src/hypercaml_interface.ml). [examples/](examples/) contains various files using HyperOCM, or conceptually related. These may have other dependencies, so may not compile. 

The main directory, [theories/](theories/), has the following contents:
* [Deprecated/](theories/Deprecated/) contains various old code, alternate implementations, and incomplete ideas. It is largely undocumented and may not work.
* [Utility/](theories/Utility/) contains utility files for Ltac2. [UTest.v](theories/Utility/UTest.v) contains a small framework for making tests in Ltac2, while the other files add extra functionality missing from the standard library.
* [HypercamlInterface.v](theories/HypercamlInterface.v) exposes Ltac2 bindings for Hypercaml's graphs and matching functions, as well as notations for efficiently inputting graphs and matches.
* [HypercamlTesting.v](theories/HypercamlTesting.v) contains unit tests for the Hypercaml bindings and implementation.
* [TensorExpr.v](theories/TensorExpr.v) contains an Ltac2 definition of abstract tensor expressions, including a normal form with sums on the outside. Can determine equivalence up to strict equality, alpha-equivalence, and full semantic equivalence. Includes testing of these functions.
* [TensorExprToGraph.v](theories/TensorExprToGraph.v) contains functions translating between tensor expressions and graphs, as well as some simple tests of correctness. 
* [TensorExprToRocq.v](theories/TensorExprToRocq.v) contains functions converting Ltac2 tensor expressions to and from Rocq terms, based on the modular development of [Summable.v](theories/Summable.v).