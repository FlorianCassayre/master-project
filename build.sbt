name := "master-project"

version := "0.1"

scalaVersion := "3.1.1"

scalacOptions ++= Seq(
  "-feature",
  "-language:implicitConversions"
)

lazy val lisa = RootProject(file("lisa"))
lazy val root = (project in file(".")).dependsOn(lisa)

libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "2.1.1"

libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.10" % "test"
