# autodiff

This is a prototype implementation of a certified automatic differentiation framework in Lean. More information can be found at the "Automatic Certified Differentiation in Lean" paper.

## Directory Structure

    autodiff/
    |- Autodiff/ ......... The implementation of the automatic differentiation framework
    |- Test/ ............. Test cases
    |- scripts/ .......... Scripts for running steps of the evaluation benchmark
    |- Main.lean ......... Lean code of the evaluation benchmark
    |- runBenchmark.sh ... Shell script for running the evaluation benchmark end-to-end

## Quick Start

An installation of Lean 4 (including `elan` and `lake`) is required.

To build the project:

`lake build`

And to run the test cases and the case study:

`lake test`

Each of the test cases uses the `#print` command to display the result of the test case, and the `#guard_msgs` command to compare it against the expected result. 

To run the benchmark:

`./runBenchmark.sh`

The script runs the benchmark over 100 randomly generated functions. This number can be changed by modifying the script (line 7).