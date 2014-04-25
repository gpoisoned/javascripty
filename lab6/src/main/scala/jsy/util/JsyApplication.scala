package jsy.util

import java.io.File

abstract class JsyApplication {
  import jsy.util.options
  
  var debug = false /* set to false to disable debugging output */
  var keepGoing = false /* set to true to keep going after exceptions */
  var maxSteps: Option[Int] = None /* set to a number to bound the number of execution steps */
  
  var anonOption = ("input",
    { case filename :: Nil => new File(filename) }: PartialFunction[List[String], File],
    "A file containing a JavaScripty program or a directory with .jsy files.")
    
  var flagOptions = List(
    ("debug", options.SetBool(b => debug = b, Some(b => debug == b)), "debugging"),
    ("keep-going", options.SetBool(b => keepGoing = b, Some(b => keepGoing == b)), "keep going after exceptions"),
    ("bound-steps", options.SetInt(
        { i => maxSteps = i },
        Some({ 
          case true => maxSteps map { i => ": %d".format(i) }
          case false => if (maxSteps == None) Some("") else None
        })),
     "bound for maximum number of execution steps before aborting")
  )
  
  def handle[T](default: T)(e: => T): T =
    if (!keepGoing) e
    else try e catch {
      case exn: Throwable => println(exn.toString); default
    }
    
  def processFile(file: File): Unit
  
  def isJsy(file: File): Boolean = {
    val jsyext = """[.]jsy$""".r
    jsyext findFirstIn file.getName match {
      case Some(_) => true
      case None => false
    }
  }
  
  def main(args: Array[String]) {
    def doFile(file: File) {
      if (file.isFile) {
        processFile(file)
      }
      else if (file.isDirectory) {
        file.listFiles filter isJsy foreach doFile
      }
      else {
        throw new IllegalArgumentException("File %s does not exist.".format(file))
      }
    }
    val opts = new options.Options("jsy", flagOptions, anonOption)
    val file: File = opts.process(args)
    doFile(file)
  }

}