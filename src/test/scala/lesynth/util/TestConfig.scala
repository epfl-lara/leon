package lesynth
package util

import java.util.logging.FileHandler
import java.util.logging.Level
import java.util.logging.SimpleFormatter

import insynth.Config

// used to configure global setting before tests are run
object TestConfig {

	// create a file handler with appropriate path (no appending)
	val inSynthHandler = new FileHandler("insynthleon.txt", true);
	// set to log all levels
	inSynthHandler.setLevel(Level.ALL);
	// set simple text formatter
	inSynthHandler.setFormatter(new SimpleFormatter);
	
	Config.setLoggerHandler(inSynthHandler)
  
  val testDir = "testcases/insynth-leon-tests/" 
    
  val synthesisTestDir = "testcases/insynth-synthesis-tests/" 
    
  val lesynthTestDir = "testcases/lesynth/test/" 
  
  val HOME_FOLDER = "/home/kuraj/"
    
  val classpathArray = Array(
    "target/scala-2.9.2/classes",
    "library/target/scala-2.9.2/classes",
    "unmanaged/64/cafebabe_2.9.2-1.2.jar",
    "unmanaged/64/scalaz3.jar",
    HOME_FOLDER + ".ivy2/cache/com.typesafe.akka/akka-actor/jars/akka-actor-2.0.4.jar",
    HOME_FOLDER + ".ivy2/cache/com.typesafe/config/bundles/config-0.3.1.jar",    
    HOME_FOLDER + ".sbt/boot/scala-2.9.2/lib/scala-library.jar",
    HOME_FOLDER + ".sbt/boot/scala-2.9.2/lib/scala-compiler.jar"
	)
}