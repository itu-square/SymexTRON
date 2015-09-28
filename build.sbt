name := "VeriTRAN"

version := "1.0"

scalaVersion := "2.11.7"

scalacOptions ++= Seq("-unchecked", "-deprecation")

libraryDependencies += "org.scalaz" %% "scalaz-core" % "7.1.3"

libraryDependencies += "org.scalaz.stream" %% "scalaz-stream" % "0.7.2a"

libraryDependencies += "com.googlecode.kiama" %% "kiama" % "1.8.0"
