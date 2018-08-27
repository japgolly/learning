name := "quantifiers"

scalaVersion := "2.12.6"

scalacOptions := List(
        "-unchecked",
        "-deprecation",
        "-Ypartial-unification",
        "-feature", "-language:postfixOps", "-language:implicitConversions", "-language:higherKinds", "-language:existentials")

libraryDependencies += "org.scalaz" %% "scalaz-core" % "7.2.24"

triggeredMessage := Watched.clearWhenTriggered
