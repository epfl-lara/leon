#!/bin/bash
exec scala "$0" "$@"
!#

def procFile(fileName: String): Unit = {
  import sys.process._

  val directory = fileName.substring(0, fileName.lastIndexOf('/'))
  // println(s"Processing ${fileName}. Directory: ${directory}")
  Seq("mkdir", "-p", "./STATS_DUMP/" + directory).!
  val loggerFile = new java.io.File("./STATS_DUMP/" + fileName + ".log")
  val logger = new FileProcessLogger(loggerFile)

  val retVal = Seq("./leon", "--pcfg-stats", fileName).!<(logger)

  logger.close
  if (retVal != 0) {
    println(s"${fileName}: ${retVal}")
  }
  // println(s"Done processing ${fileName}")
}

// args.par.foreach(procFile)
args.par.foreach(procFile)