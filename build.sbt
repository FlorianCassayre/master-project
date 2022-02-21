name := "master-project"

version := "0.1"

scalaVersion := "2.13.8"

lazy val lisa = RootProject(file("lisa"))
lazy val root = (project in file(".")).dependsOn(lisa)
