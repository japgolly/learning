name := "Recursion blog series"

scalaVersion := "2.12.4"

scalacOptions := List(
	"-unchecked",
	"-deprecation",
  "-Xsource:2.13",
	"-Ypartial-unification",
	"-Ypatmat-exhaust-depth", "off",
	"-Ywarn-inaccessible",
	"-feature", "-language:postfixOps", "-language:implicitConversions", "-language:higherKinds", "-language:existentials")

addCompilerPlugin("org.spire-math" %% "kind-projector" % "0.9.4")

libraryDependencies += "com.github.japgolly.microlibs" %% "recursion" % "1.12"
libraryDependencies += "com.slamdata" %% "matryoshka-core" % "0.21.2"

enablePlugins(JmhPlugin)
fork := true
javaOptions ++= Seq("-server", "-Xss20M")

triggeredMessage := Watched.clearWhenTriggered
addCommandAlias("c",  "compile")
addCommandAlias("tc", "test:compile")
addCommandAlias("t",  "test")
