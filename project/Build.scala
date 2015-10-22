import sbt._

object GitHub {
  def project(p : String) = RootProject(uri(s"https://github.com/$p.git"))
}

object Dependencies extends Build {
  lazy val root = Project("root", file(".")).dependsOn(smt_lib)

  lazy val smt_lib = GitHub.project("regb/scala-smtlib")

}
