scalaVersion := "2.11.8"

scalacOptions ++= Seq(
  "-deprecation",
  "-unchecked",
  "-Ywarn-dead-code",
  "-Ywarn-unused",
  "-Ywarn-value-discard",
  "-feature",
  "-language:postfixOps",
  "-language:implicitConversions",
  "-language:higherKinds",
  "-language:existentials")

libraryDependencies ++= Seq(
  "com.github.japgolly.microlibs" %% "recursion" % "1.5",
  "com.github.japgolly.nyaya"     %% "nyaya-gen" % "0.8.1",
  "com.typesafe.play"             %% "play-json" % "2.5.10")

