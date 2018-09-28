name := "Learning"

scalaVersion := "2.12.6"

scalacOptions := List(
	"-unchecked",
	"-deprecation",
  "-Xsource:2.13",
	"-Ypartial-unification",
	"-Ypatmat-exhaust-depth", "off",
	"-Ywarn-inaccessible",
	"-feature", "-language:postfixOps", "-language:implicitConversions", "-language:higherKinds", "-language:existentials")

addCompilerPlugin("org.spire-math" %% "kind-projector" % "0.9.7")

libraryDependencies += "org.scalaz" %% "scalaz-core" % "7.2.26"
