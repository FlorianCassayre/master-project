lazy val root = (project in file("."))
  .settings(
    commonSettings,
    name := "master-project",
    organization := "me.cassayre.florian",
    version := "0.2.0",
    versionScheme := Some("semver-spec"),
    scalaVersion := "3.1.3-RC1-bin-20220410-220b753-NIGHTLY",
    scalacOptions ++= Seq(
      "-feature",
      "-language:implicitConversions"
    ),
    libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "2.1.1",
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.10" % "test",
    console / initialCommands := "import me.cassayre.florian.masterproject.front.*"
  )
  .dependsOn(lisa)

lazy val lisa = (project in file("lisa")).settings(commonSettings)

lazy val commonSettings = Seq(
  publishTo := Some(MavenCache("local-maven", file("releases"))),
  Compile / packageDoc / publishArtifact := false,
  //packageDoc / publishArtifact := false,
  Compile / doc / sources := Seq.empty,
)
