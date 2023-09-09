# Formalising Mathematics

This repository contains formal proofs of three mathematical theorems using
the Lean programming language. The theorems are some of the most fundamental
statements in mathematical analysis:

- Intermediate Value Theorem
- Vitali's Theorem
- Banach-Steinhaus Theorem.

Many thanks to Professor Kevin Buzzard for teaching me how to write production-level
Lean code and guiding me along the way of building those three projects as a part
of the Formalising Mathematics course at Imperial College London in Spring 2023.

I also wanted to thank the [Mathlib](https://github.com/leanprover-community/mathlib)
community for building the library allowing for proving undergraduate-level
mathematical theorems using Lean.

## Project Structure

The **reports** directory contains tex source files and generated pdf reports
stating written proofs of the theorems and documenting the process of formalising
them using Lean.

The **src** directory contains all source files with the formal proofs of the
theorems.

## Getting Started

The idea behind using Lean to prove mathematical statements can be compared to
the compilation process of any other programming language. The main difference
is that a usual program is compiled so that it can then be run and do something.

In case of Lean however, all we are interested in is the compilation process.
If the formal proof that we have programmed compiles successfully, it means that
it is correct. That is achieved by encapsulating all details of the mathematical
way of reasoning into the semantics of the language.

Below you can find instructions on how to get the environment set up and run
the compilation on the source files to check that the proofs are correct.

### Setting up Lean

You can install Lean by following the docs [here](https://leanprover-community.github.io/get_started.html)

If you are running Arch linux you can also follow the instructions [here](https://wiki.archlinux.org/title/Lean_Theorem_Prover#:~:text=exe%20cache%20get-,Lean%203%20via%20the%20AUR,-Install%20lean%2Dcommunity)

This will let you download Lean 3 from AUR and also show how to initialise the project.

### Getting Access to the Mathlib Library

You need to download Mathlib library so that the code that relies on it works.
Assuming you have followed the steps above, you can get access to that dependency
by running:

```
leanproject pull
```

This will go to github and download the latest version of mathlib to your project.

### IDE setup

There is a VS Code extension for Lean, however I don't have that much experience
using it. You can find my setup for neovim below:

The example below shows configuration using Packer as the neovim package manager.

Add the following to your packer startup configuration:

```
  use 'Julian/lean.nvim'
```

After that you need to import and configure the LSP plugin in your file responsible for lsp
configuration:

```
local lean = require 'lean'
lean.setup{
  abbreviations = { builtin = true },
  lsp = { on_attach = on_attach },
  lsp3 = { on_attach = on_attach },
  mappings = true,
}
```

Now that your IDE is set up you can open any of the files in src and you should
see the language server compiling the code and checking if everything works.




