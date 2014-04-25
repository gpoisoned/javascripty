import Lab6._
import org.scalatest._
import jsy.lab6.ast._

class Lab6Spec extends FlatSpec {
  
  val strings = List(
     "",
     "a",
     "aa",
     "aaa",
     "aaaa",
     "abab",
     "abbb",
     "aaaaa",
     "abbaabbaab",
     "aaaaaa",
     "aba",
     "bba",
     "ba",
     "b"
  )

  val respecs = Map(1 -> List(
    "a",
    "b",
    ".",
    "aa",
    "a.",
    "!",
    "!a",
    "!!",
    "a?",
    "a???"
  ), 2 -> List(
    "a*",
    "a+",
    "aa*",
    "(aa)*",
    "a(a.)*",
    "a(..)*"
  ), 3 -> List(
    "#|a",
    "#|a|b",
    "(a|b)*",
    "(a*|b)*",
    "(#|a)*"
  ), 4 -> List(
    "a**",
    "(a|b)**", 
    "(a*|b*)*",
    "a?*+"
  ), 5 -> List(
    "~a(..)*",
    "~a(~..)*",
    "~!",
    "~#",
    "a&.",
    "...&a*",
    "(..)*&a*b&.b*",
    "(..)*&a*b&~.b*",
    "(..)*&a*b&~.b*",
    "~(~aba)",
    "~((~a)*(b|(a&.)))"
  ))
  
  val respecsast = respecs mapValues { l => l map { s => (s, jsy.lab6.RegExprParser.parse(s)) } }
  
  def assertRefRetest(re: RegExpr, str: String) {
    assertResult(jsy.lab6.Lab6Reference.retest(re, str)) { retest(re, str) }
  }
  
  "parse/respecs1" should "should produce the appropriate RegExpr AST" in {
    for ((str,re) <- respecsast(1)) assertResult(re) { RegExprParser.parse(str) }
  }

  "parse/respecs2" should "should produce the appropriate RegExpr AST" in {
    for ((str,re) <- respecsast(2)) assertResult(re) { RegExprParser.parse(str) }
  }

  "parse/respecs3" should "should produce the appropriate RegExpr AST" in {
    for ((str,re) <- respecsast(3)) assertResult(re) { RegExprParser.parse(str) }
  }

  "parse/respecs4" should "should produce the appropriate RegExpr AST" in {
    for ((str,re) <- respecsast(4)) assertResult(re) { RegExprParser.parse(str) }
  }

  "parse/respecs5" should "should produce the appropriate RegExpr AST" in {
    for ((str,re) <- respecsast(5)) assertResult(re) { RegExprParser.parse(str) }
  }

  "retest/respecs1" should "should perform regular expression matching" in {
    for ((_,re) <- respecsast(1)) {
      for (s <- strings) assertRefRetest(re, s)
    }
  }

  "retest/respecs2" should "should perform regular expression matching" in {
    for ((_,re) <- respecsast(2)) {
      for (s <- strings) assertRefRetest(re, s)
    }
  }

  "retest/respecs3" should "should perform regular expression matching" in {
    for ((_,re) <- respecsast(3)) {
      for (s <- strings) assertRefRetest(re, s)
    }
  }

  "retest/respecs4" should "should perform regular expression matching" in {
    for ((_,re) <- respecsast(4)) {
      for (s <- strings) assertRefRetest(re, s)
    }
  }
  
  "retest/respecs5" should "should perform regular expression matching (Extra Credit)" in {
    for ((_,re) <- respecsast(5)) {
      for (s <- strings) assertRefRetest(re, s)
    }
  }

}
