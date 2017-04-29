name := course.value + "-" + assignment.value

scalaVersion := "2.11.7"

scalacOptions ++= Seq("-deprecation")

// grading libraries
libraryDependencies += "junit" % "junit" % "4.10" % "test"
libraryDependencies ++= assignmentsMap.value.values.flatMap(_.dependencies).toSeq

// include the common dir
commonSourcePackages += "common"

courseId := "PeZYFz-zEeWB_AoW1KYI4Q"

val depsQuickcheck = Seq("org.scalacheck" %% "scalacheck" % "1.12.1")

assignmentsMap := {
  val styleSheetPath = (baseDirectory.value / ".." / ".." / "project" / "scalastyle_config.xml").getPath
  Map(
    "example" -> Assignment(
      packageName = "example",
      key = "lLkU5d7xEeWGkg7lknKHZw",
      itemId = "AYDPu",
      partId = "5QFuy",
      maxScore = 10d,
      styleScoreRatio = 0.2,
      styleSheet = styleSheetPath),
    "streams" -> Assignment(
      packageName = "streams",
      key = "2iZL1kBCEeWwdxI8PoEnkw",
      itemId = "Sh2dW",
      partId = "EKNhX",
      maxScore = 10d,
      styleScoreRatio = 0.2,
      styleSheet = styleSheetPath,
      options = Map("grader-timeout" -> "1800", "Xms" -> "512m", "Xmx" -> "512m", "totalTimeout" -> "1500", "individualTimeout" -> "600")),
    "quickcheck" -> Assignment(
      packageName = "quickcheck",
      key = "l86W1kt6EeWKvAo5SY6hHw",
      itemId = "DF4y7",
      partId = "DZTNG",
      maxScore = 10d,
      styleScoreRatio = 0.2,
      styleSheet = styleSheetPath,
      dependencies = depsQuickcheck),
    "calculator" -> Assignment(
      packageName = "calculator",
      key = "QWry5Q33EeaVNg5usvFqrw",
      itemId = "sO8Cf",
      partId = "9eOy7",
      maxScore = 10d,
      styleScoreRatio = 0.2,
      styleSheet = (baseDirectory.value / "scalastyle" / "calculator.xml").getPath )
  )
}
