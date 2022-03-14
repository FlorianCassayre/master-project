# Florian Cassayre's Master Project

This repository hosts the work related to my Master Project (PDM) at [LARA](https://lara.epfl.ch/w/).
This includes source code, writeup and any other significant resource related to the project.

Original project title: ***Automation for Proof Assistant***

Dates: **21.02.2022** to **24.06.2022**

Tentative content:
In this project I will be working on a proof assistant ([LISA](https://github.com/epfl-lara/lisa)),
in particular I will be designing a higher-level interface to represent and write proofs.

## Compilation and execution

The Scala project depends on LISA (included as a git submodule) and runs on the same
version to avoid problems. The relevant commands are:

* `sbt test` to run the tests


<details>
  <summary>Updating LISA</summary>

  The git submodule depends on a specific commit, thus when LISA is updated _and_ we would like
  to benefit from the changes, we should execute the following commands:

  ```bash
  cd lisa
  git pull origin main
  cd ..
  git add lisa
  git commit lisa
  ```

  (make sure to rebuild the entire project after that, to avoid potential issues with incremental compilation)

</details>
