incOptions := incOptions.value.withNameHashing(true)

scalaVersion := "2.11.1"

scalacOptions ++= Seq("-unchecked", "-deprecation", "-Xcheckinit",
  "-feature", "-language:postfixOps", "-language:implicitConversions", "-language:higherKinds", "-language:existentials")

libraryDependencies ++= Seq(
  "org.scalaz"     %% "scalaz-core" % "7.0.6",
  "org.scalacheck" %% "scalacheck"  % "1.11.4"  % "test",
  "org.specs2"     %% "specs2"      % "2.3.12"  % "test")
