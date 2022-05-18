import sbt._
import Keys._
import sys.process.{Process => SysProc, ProcessLogger}
import java.util.concurrent._
import collection.mutable.ListBuffer
import scala.pickling.Defaults._
import scala.pickling.json._

final case class GradingSummary(score: Int, maxScore: Int, feedback: String)

object ScalaTestRunner {

  class LimitedStringBuffer {
    val buf = new ListBuffer[String]()
    private var lines = 0
    private var lengthCropped = false

    override def toString = buf.mkString("\n").trim

    def append(s: String) =
      if (lines < Settings.maxOutputLines) {
        val shortS =
          if (s.length > Settings.maxOutputLineLength) {
            if (!lengthCropped) {
              val msg =
                """WARNING: OUTPUT LINES CROPPED
                  |Your program generates very long lines on the standard (or error) output. Some of
                  |the lines have been cropped.
                  |This should not have an impact on your grade or the grading process; however it is
                  |bad style to leave `print` statements in production code, so consider removing and
                  |replacing them by proper tests.
                  | """.stripMargin
              buf.prepend(msg)
              lengthCropped = true
            }
            s.substring(0, Settings.maxOutputLineLength)
          } else s
        buf.append(shortS)
        lines += 1
      } else if (lines == Settings.maxOutputLines) {
        val msg =
          """WARNING: PROGRAM OUTPUT TOO LONG
            |Your program generates massive amounts of data on the standard (or error) output.
            |You are probably using `print` statements to debug your code.
            |This should not have an impact on your grade or the grading process; however it is
            |bad style to leave `print` statements in production code, so consider removing and
            |replacing them by proper tests.
            | """.stripMargin
        buf.prepend(msg)
        lines += 1
      }
  }

  private def forkProcess(proc: SysProc, timeout: Int): Unit = {
    val executor = Executors.newSingleThreadExecutor()
    val future: Future[Unit] = executor.submit(new Callable[Unit] {
      def call {
        proc.exitValue()
      }
    })
    try {
      future.get(timeout, TimeUnit.SECONDS)
    } catch {
      case to: TimeoutException =>
        future.cancel(true)
        throw to
    } finally {
      executor.shutdown()
    }
  }

  private def runPathString(file: File) = file.getAbsolutePath.replace(" ", "\\ ")

  private def invokeScalaTestInSeparateProcess(scalaTestCommand: List[String], logError: String => Unit): String = {
    val out = new LimitedStringBuffer()
    var proc: SysProc = null
    try {
      proc = SysProc(scalaTestCommand).run(ProcessLogger(out.append, out.append))
      forkProcess(proc, Settings.scalaTestTimeout)
    } catch {
      case e: TimeoutException =>
        val msg = "Timeout when running ScalaTest\n" + out.toString()
        logError(msg)
        proc.destroy()
        sys.error(msg)
      case e: Throwable =>
        val msg = "Error occurred while running the ScalaTest command\n" + e.toString + "\n" + out.toString()
        logError(msg)
        proc.destroy()
        throw e
    } finally {
      println(out.toString)
      if (proc != null) {
        println("Exit process: " + proc.exitValue())
      }
    }

    val runLog = out.toString
    runLog
  }

  private def inovkeSummaryProcess(outFilePath: String, classpathString: String, logError: String => Unit): String = {
    val summaryFilePath = outFilePath + ".summary"
    val summaryCmd = "java" ::
      "-cp" :: classpathString ::
      "ch.epfl.lamp.grading.GradingSummaryRunner" ::
      outFilePath :: summaryFilePath :: Nil
    var summaryProc: SysProc = null
    try {
      summaryProc = SysProc(summaryCmd).run()
      summaryProc.exitValue
    } catch {
      case e: Throwable =>
        val msg = "Error occurred while running the test ScalaTest summary command\n" + e.toString
        logError(msg)
        summaryProc.destroy()
        throw e
    } /* finally { // Useful for debugging when Coursera kills our grader
      println(scala.io.Source.fromFile(outFilePath).getLines().mkString("\n"))
      println(scala.io.Source.fromFile(summaryFilePath).getLines().mkString("\n"))
    }*/
    // Example output:
    // {
    //   "$type": "ch.epfl.lamp.grading.Entry.SuiteStart",
    //   "suiteId": "ParallelCountChangeSuite::50"
    // }
    summaryFilePath
  }

  def runScalaTest(classpath: Classpath, testClasses: File, outfile: File,
                   resourceFiles: List[File], javaSystemProperties: Traversable[(String, String)],
                   logError: String => Unit) = {

    // invoke scalatest in the separate process
    val classpathString = classpath map { case Attributed(file) => file.getAbsolutePath } mkString ":"
    val cmd = scalaTestCommand(testClasses, outfile, resourceFiles, javaSystemProperties, classpathString)
    val runLog = invokeScalaTestInSeparateProcess(cmd, logError)

    // compute the summary
    val summaryFilePath = inovkeSummaryProcess(outfile.getAbsolutePath, classpathString, logError)
    val summary = unpickleSummary(logError, runLog, summaryFilePath)

    // cleanup all the files
    IO.delete(new File(summaryFilePath) :: outfile :: Nil)

    (summary.score, summary.maxScore, summary.feedback, runLog)
  }

  private def unpickleSummary(logError: (String) => Unit, runLog: String, summaryFileStr: String): GradingSummary = {
    try {
      io.Source.fromFile(summaryFileStr).getLines.mkString("\n").unpickle[GradingSummary]
    } catch {
      case e: Throwable =>
        val msg = "Error occured while reading ScalaTest summary file\n" + e.toString + "\n" + runLog
        logError(msg)
        throw e
    }
  }

  private def scalaTestCommand(testClasses: File, outfile: File, resourceFiles: List[File], javaSystemProperties: Traversable[(String, String)], classpathString: String): List[String] = {
    val testRunPath = runPathString(testClasses)
    val resourceFilesString = resourceFiles.map(_.getAbsolutePath).mkString(":")
    // Deleting the file is helpful: it makes reading the file below crash in case ScalaTest doesn't
    // run as expected. Problem is, it's hard to detect if ScalaTest ran successfully or not: it
    // exits with non-zero if there are failed tests, and also if it crashes...
    outfile.delete()

    def prop(name: String, value: String) = "-D" + name + "=" + value

    // we don't specify "-w packageToTest" - the build file only compiles the tests
    // for the current project. so we don't need to do it again here.
    "java" ::
      prop(Settings.scalaTestReportFileProperty, outfile.getAbsolutePath) ::
      prop(Settings.scalaTestIndividualTestTimeoutProperty, Settings.individualTestTimeout.toString) ::
      prop(Settings.scalaTestReadableFilesProperty, resourceFilesString) ::
      prop(Settings.scalaTestDefaultWeightProperty, Settings.scalaTestDefaultWeight.toString) ::
      javaSystemProperties.map((prop _).tupled).toList :::
      "-cp" :: classpathString ::
      "org.scalatest.tools.Runner" ::
      "-R" :: testRunPath ::
      "-C" :: Settings.scalaTestReporter ::
      Nil
  }

  def scalaTestGrade(gradingReporter: GradingFeedback, classpath: Classpath, testClasses: File, outfile: File,
                     resourceFiles: List[File], javaSystemProperties: Traversable[(String, String)]): Unit = {

    val (score, maxScore, feedback, runLog) =
      runScalaTest(classpath, testClasses, outfile, resourceFiles, javaSystemProperties, gradingReporter.testExecutionFailed)

    if (score == maxScore) {
      gradingReporter.allTestsPassed()
    } else {
      val scaledScore = gradingReporter.maxTestScore * score / maxScore
      gradingReporter.testsFailed(feedback, scaledScore)
    }

    if (!runLog.isEmpty) {
      gradingReporter.testExecutionDebugLog(runLog)
    }
  }
}

