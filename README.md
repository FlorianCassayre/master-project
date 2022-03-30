# Florian Cassayre's Master Project

This repository hosts the work related to my Master Project (PDM) at [LARA](https://lara.epfl.ch/w/).
This includes source code, writeup and any other significant resource related to the project.

Project title: ***A Proof System for LISA***

Dates: **21.02.2022** to **24.06.2022**

Content:
In this project I will be working on a proof assistant ([LISA](https://github.com/epfl-lara/lisa)),
in particular I will be designing a higher-level interface to represent and write proofs.

## Installation as a library

The repository can be used as a sbt dependency.
Since LISA is not yet published, _you_ are responsible for including LISA in your project as a dependency.

Details on how to do so are described below.

<details>
  <summary>Installing LISA</summary>

There are two main possibilities for installing LISA.
In either case, it's very important that the version of LISA matches the one used by this project,
otherwise you might encounter incompatibilities.

Assuming you are in your project's directory and `$COMMIT` is the hash of the desired commit in LISA:

* **sbt managed dependency** (easiest):
  * Add the following in your `build.sbt` (or adapt your existing configuration):
    ```sbt
    lazy val lisa = ProjectRef(uri("https://github.com/epfl-lara/lisa.git#$COMMIT"), "lisa")
    
    lazy val root = (project in file(".")).dependsOn(lisa)
    ```
* **git repository or submodule** (if you need to develop on LISA at the same time):
  * If your project **is already** a git repository, then you can add LISA as a submodule:
    ```
    git submodule add git@github.com:epfl-lara/lisa.git lisa
    cd lisa
    git checkout $COMMIT
    cd ..
    git commit
    ```
  * If your project **is not** a git repository, then you can clone it locally:
    ```
    git clone git@github.com:epfl-lara/lisa.git
    cd lisa
    git checkout $COMMIT
    cd ..
    ```

The table below indicates the version compatibility (= value of `$COMMIT`):

| `master-project` |                   `lisa`                   |
|:----------------:|:------------------------------------------:|
|     `0.1.0`      | `eacb9c06aa2975b9ae2bc993847c597eb3c54995` |

</details>

Then, add these two lines to your `build.sbt`:
```sbt
resolvers += "Florian Cassayre" at "https://maven.cassayre.me"

libraryDependencies += "me.cassayre.florian" %% "master-project" % "0.1.0"
```

Or alternatively, if you would like to include it from the sources:

```sbt
lazy val lisa = ???
lazy val masterproject = ProjectRef(uri("https://github.com/FlorianCassayre/master-project.git#$COMMIT"), "lisa")

lazy val root = (project in file(".")).dependsOn(lisa, masterproject)
```

(replace `$COMMIT` by the commit hash)

## Development

The Scala project depends on LISA, included as a git submodule:
make sure to run `git submodule update --init --recursive` the first time.
It runs on the same Scala/sbt versions as LISA to avoid problems.

The relevant commands are:

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

  (make sure to rebuild the entire project after this operation, to avoid potential issues with incremental compilation)

</details>

## Licensing

This project is licensed under the _MIT License_.

LISA is licensed under the _Apache License 2.0_.
