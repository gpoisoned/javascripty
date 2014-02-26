object Lab2 extends jsy.util.JsyApplication {
  import jsy.lab2.Parser
  import jsy.lab2.ast._
  
  /*
   * CSCI 3155: Lab 2
   * <Jiwan Rana>
   * 
   * Partner: <Michael Winterfeld>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace 'YourIdentiKey' in the object name above with your IdentiKey.
   * 
   * Replace the 'throw new UnsupportedOperationException' expression with
   * your code in each function.
   * 
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your lab will not be graded if it does not compile.
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert.  Simply put in a
   * 'throws new UnsupportedOperationException' as needed to get something
   * that compiles without error.
   */
  
  /* We represent a variable environment is as a map from a string of the
   * variable name to the value to which it is bound.
   * 
   * You may use the following provided helper functions to manipulate
   * environments, which are just thin wrappers around the Map type
   * in the Scala standard library.  You can use the Scala standard
   * library directly, but these are the only interfaces that you
   * need.
   */
  
  type Env = Map[String, Expr]
  val emp: Env = Map()
  def get(env: Env, x: String): Expr = env(x)
  def extend(env: Env, x: String, v: Expr): Env = {
    require(isValue(v))
    env + (x -> v)
  }
  
  /* Some useful Scala methods for working with Scala values include:
   * - Double.NaN
   * - s.toDouble (for s: String)
   * - n.isNaN (for n: Double)
   * - n.isWhole (for n: Double)
   * - s (for n: Double)
   * - s format n (for s: String [a format string like for printf], n: Double)
   */

  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case B(b) =>if(b) 1 else 0
      case S(s) => try { s.toDouble } catch { case _: NumberFormatException => Double.NaN }
  	  case Undefined => Double.NaN
    }
  }
  
  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case Undefined =>false
      case B(b) => b
      case N(n) if n.isNaN => false
      case N(n) => if (n ==0 || n == -0.0) false else true
      case S(str) => if (str.isEmpty) false else true
      case _ => throw new UnsupportedOperationException 
    }
  }
  /*
  println(toBoolean(N(Double.NaN)))
  println(toBoolean(N(0.0)))
  println(toBoolean(N(1.5)))
  println(toBoolean(S("")))
  println(toBoolean(S("3")))
  */
  
  
  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
      case Undefined => "undefined"
      case N(n) => if (n.isWhole) "%.0f" format n else n.toString
      case B(b) => if (b) "true" else "false" 
    }
  }
  
  def eval(env: Env, e: Expr): Expr = {
    //println(e)
    /* Some helper functions for convenience. */
    def eToVal(e: Expr): Expr = eval(env, e)

    e match {
      /* Base Cases */
      case N(n) => N(n)
      case B(b) => B(b)
      case S(str) => S(str)
      case Var(x) => get(env,x)
      case Undefined => Undefined
      
      /* Inductive Cases */
      case Print(e1) => println(pretty(eToVal(e1))); Undefined

      case Binary(And,e1,e2) => if(toBoolean(eval(env,e1))) eval(env,e2) else eval(env,e1)    
      case Binary(Or,e1,e2) => if(toBoolean(eval(env,e1))) eval(env,e1) else eval(env,e2)
      case Binary(Plus,e1,e2) =>{
        val (v1,v2) = (eToVal(e1), eToVal(e2))
        (v1,v2) match{
          //case (N(_),N(_)) => N(toNumber(v1) + toNumber(v2))
          //case (B(_),N(_)) | (N(_),B(_)) | (B(_),B(_)) => N(toNumber(v1) + toNumber(v2))
          case (S(_),_) | (_,S(_)) => S(toStr(v1).concat(toStr(v2)))
          case _ => N(toNumber(v1) + toNumber(v2))
        }
      }     
      
     case Binary(Minus,e1,e2) =>N(toNumber(eToVal(e1)) - toNumber(eToVal(e2)))            
     case Binary(Times,e1,e2) =>  N(toNumber(eToVal(e1)) * toNumber(eToVal(e2)))
     
     case Binary(Div,e1,e2) => N(toNumber(eToVal(e1)) / toNumber(eToVal(e2)))
     case Binary(Eq,e1,e2) =>if (toNumber(eToVal(e1)) == toNumber(eToVal(e2))) B(true) else B(false)
     case Binary(Ne,e1,e2) =>if (toNumber(eToVal(e1)) == toNumber(eToVal(e2))) B(false) else B(true)
     case Binary(Lt,e1,e2) =>{ (e1,e2) match{
       case (S(_),S(_)) =>  if (toStr(eToVal(e1)) < toStr(eToVal(e2))) B(true) else B(false)
       case (_,_) => if (toNumber(eToVal(e1)) < toNumber(eToVal(e2))) B(true) else B(false) 
     	}    
     }
     case Binary(Le,e1,e2) => if (toNumber(eToVal(e1)) <= toNumber(eToVal(e2))) B(true) else B(false)
     case Binary(Gt,e1,e2) => if(toNumber(eToVal(e1)) > toNumber(eToVal(e2))) B(true) else B(false)
     case Binary(Ge,e1,e2) => if(toNumber(eToVal(e1)) >= toNumber(eToVal(e2))) B(true) else B(false)
     
     case If(e1,e2,e3) => if(toBoolean(eToVal(e1)) == true) eToVal(e2) else eToVal(e3)
     case Binary(Seq,e1,e2) => eToVal(e2)
     
     case Unary(Neg,e) => N(-1*toNumber(eToVal(e)))
     case Unary(Not,e) => val v = toBoolean(eToVal(e)); if(v) B(false) else B(true);
     
     case ConstDecl(x, e1, e2) => eval(extend(env, x, eToVal(e1)), e2)
    }
  }
  
  
  
  // Interface to run your interpreter starting from an empty environment.
  def eval(e: Expr): Expr = eval(emp, e)

  // Interface to run your interpreter from a string.  This is convenient
  // for unit testing.
  def eval(s: String): Expr = eval(Parser.parse(s))

 /* Interface to run your interpreter from the command-line.  You can ignore what's below. */ 
 def processFile(file: java.io.File) {
    if (debug) { println("Parsing ...") }
    
    val expr = Parser.parseFile(file)
    
    if (debug) {
      println("\nExpression AST:\n  " + expr)
      println("------------------------------------------------------------")
    }
    
    if (debug) { println("Evaluating ...") }

    val v = eval(expr)
    
    println(pretty(v))
  }

}