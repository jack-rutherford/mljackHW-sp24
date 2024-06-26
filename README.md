# Jack Code Generator
### Author: Jack Rutherford

This README provides an overview of the `jack.sml` code and explains the `codegen` function and the `create_bindings` functions.

## Introduction

What I accomplished for this project was primarily altering the `jack.sml: codegen` function to implement all the different datatypes found in `jack.grm`. 

This function recursively traverses the AST to analyze the structure of the program and generate appropriate code according to the type of the AST node. This code generation includes making bindings, printing to the outfile, and calling codegenlist/codegen for the recursive traversal.

You utilize this by being in the mljack-hw24 directory and typing `jack` into the terminal, and then the path to the `.jack` file you want to compile.

Example: 
```
> jack 
> Seven/Main.jack
> diff Seven/Main.vm Seven/Main.vm.goal
```

## Codegen Function

The `codegen` function is the main function responsible for generating code from a `.jack` file. It takes the abstract syntax tree (AST) of the input file as a parameter and produces the appropriate code.

The `codegen` function performs various tasks, including:

1. Traversing the AST: It recursively traverses the AST to analyze the structure of the program and generate code accordingly.

2. Handling Classes: It handles class declarations, including generating code for class variables, methods, and constructors.

3. Managing Variables: It generates code for variable declarations, assignments, and accessing variables within the scope of a class or method.

4. Handling Expressions: It generates code for expressions, such as arithmetic operations, logical operations, and function calls.

5. Generating Output: It generates the final output code to the outfil based on the analyzed AST.

## What I accomplished

Many of these methods are simple, such as `and'` where it calls `codegen` on the two expressions taken as parameters, and prints out **"and\n"** to the outfile to perform a boolean logic operation between the two expressions. Many are more complex, however, utilizing the different bindings created in the `create_bindings` functions to generate the correct code for the given datatype. Some of the methods are more complex, such as the constructor method, which generates the code for a constructor in a class by creating bindings for the parameters and local variables, and making `bindingsNew` which appends the parameter bindings to the local bindings and the rest of bindings. We then output the appropriate code that declares the function with the classname, the id, and the number of local variables, then print out a constant with the number of bindings, allocate memory, and "`pop pointer 0`". Then finishing it off by calling `codegenlist` with an updated parameter of all of the new bindings that we just created.

A lot of the following methods that are a part of `codegen` have a similar makeup/structure, with the more complex codegen methods having lambda functions (like `if'`, `ifelse'`, `while`, etc). Overall, altering the `codegen` function in `jack.sml` was a mix of utilizing knowledge from the lectures and slides, and comparing my .vm code with the .vm.goal, and altering the sml appropriately.
