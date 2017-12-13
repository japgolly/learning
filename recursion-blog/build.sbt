name := "Recursion blog series"

lazy val commonSettings = Seq[Setting[_]](

  scalaVersion := "2.12.4",

  scalacOptions := List(
    "-unchecked",
    "-deprecation",
    "-Xsource:2.13",
    "-Ypartial-unification",
    "-Ypatmat-exhaust-depth", "off",
    "-Ywarn-inaccessible",
    "-feature", "-language:postfixOps", "-language:implicitConversions", "-language:higherKinds", "-language:existentials"),

  addCompilerPlugin("org.spire-math" %% "kind-projector" % "0.9.5"),

  triggeredMessage := Watched.clearWhenTriggered) ++
  addCommandAlias("cc", ";clean;compile") ++
  addCommandAlias("c", "compile") ++
  addCommandAlias("tc", "test:compile") ++
  addCommandAlias("t", "test")

lazy val root = (project in file("."))
  .aggregate(example, bench)
  .settings(commonSettings)

lazy val example = project
  .settings(
    commonSettings,
    libraryDependencies += "org.scalaz" %% "scalaz-core" % "7.2.17")

lazy val bench = project
  .enablePlugins(JmhPlugin)
  .dependsOn(example)
  .settings(
    commonSettings,
    libraryDependencies += "com.github.japgolly.microlibs" %% "recursion" % "1.13",
    libraryDependencies += "com.slamdata" %% "matryoshka-core" % "0.21.2",
    fork := true,
    javaOptions ++= Seq("-server", "-Xss20M"))

