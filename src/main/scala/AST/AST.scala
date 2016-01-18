package AST

object Priority {
    val binary = Map("lambda"->1,
                     "or"->2,
                     "and"->3,
                     "is"->8, "<"->8, ">"->8, ">="->8, "<="->8, "=="->8, "!="->8,
                     "+"->9,  "-"->9,
                     "*"->10, "/"->10, "%"->10,
                     "**"->11)

    val unary = Map("not"->4,
                    "+"->12,  "-"->12)
}

sealed abstract class Node {
    def toStr = "error: toStr not implemented"
    val indent = " " * 4
}

case class IntNum(value: Integer) extends Node {
    override def toStr = value.toString
}

case class FloatNum(value: Double) extends Node {
    override def toStr = value.toString
}

case class StringConst(value: String) extends Node {
    override def toStr = value
}

case class TrueConst() extends Node {
    override def toStr = "True"
}

case class FalseConst() extends Node {
    override def toStr = "False"
}

case class Variable(name: String) extends Node {
    override def toStr = name
}

case class Unary(op: String, expr: Node) extends Node {

    override def toStr = {
        var str  = expr.toStr
        expr match {
            case e@BinExpr(_,_,_) => if(Priority.binary(e.op)<=Priority.unary(op)) { str = "(" + str + ")" }
            case e@Unary(_,_) => if(Priority.unary(e.op)<=Priority.unary(op)) { str = "(" + str + ")" }
            case _ =>
        }
        op + " " + str
    }

}

case class BinExpr(op: String, left: Node, right: Node) extends Node {

    override def toStr = {
        var leftStr  = left.toStr
        var rightStr = right.toStr
        left match {
            case l@(_:BinExpr) => if(Priority.binary(l.op)<Priority.binary(op)) { leftStr = "(" + leftStr + ")" }
            case l@(_:Unary) => if(Priority.unary(l.op)<Priority.binary(op)) { leftStr = "(" + leftStr + ")" }
            case _ =>
        }
        right match {
            case r@BinExpr(_,_,_) => if(Priority.binary(r.op)<Priority.binary(op)) { rightStr = "(" + rightStr + ")" }
            case r@Unary(_,_) => if(Priority.unary(r.op)<Priority.binary(op)) { rightStr = "(" + rightStr + ")" }
            case _ =>
        }
        leftStr + " " + op + " " + rightStr
    }
}

case class IfElseExpr(cond: Node, left: Node, right: Node) extends Node {
    override def toStr = left.toStr + " if " + cond.toStr + " else " + right.toStr
}

case class Assignment(left: Node, right: Node) extends Node {
    override def toStr = left.toStr + " = " + right.toStr
}

case class Subscription(expr: Node, sub: Node) extends Node {
    override def toStr = expr.toStr + "[" + sub.toStr + "]"
}

case class KeyDatum(key: Node, value: Node) extends Node {
    override def toStr = key.toStr + ": " + value.toStr
}

case class GetAttr(expr:Node, attr: String) extends Node {
    override def toStr = expr.toStr + "." + attr
}

case class ConditionalSuite(cond: Node, suite: Node)

case class IfElifElseInstruction(ifClause: ConditionalSuite, elifClauses: List[ConditionalSuite], elseClause: Option[Node]) extends Node {
    override def toStr = {
      var str = formatConditionalClause("if")(ifClause) + elifClauses.map(formatConditionalClause("\nelif")).mkString
      if (elseClause isDefined) str += "\nelse:\n" + elseClause.get.toStr.replaceAll("(?m)^", indent)
      str
    }

    private def formatConditionalClause(instruction:String)(clause: ConditionalSuite) =
      instruction + clause.cond + ":\n" + clause.suite.toStr.replaceAll("(?m)^", indent)
}

case class WhileInstr(cond: Node, body: Node) extends Node {
    override def toStr = {
        "while " + cond.toStr + ":\n" + body.toStr.replaceAll("(?m)^", indent)
    }
}

case class InputInstr() extends Node {
    override def toStr = "input()"
}

case class ReturnInstr(expr: Node) extends Node {
    override def toStr = "return " + expr.toStr
}

case class PrintInstr(expr: Node) extends Node {
    override def toStr = "print " + expr.toStr
}

case class FunCall(name: Node, args_list: Node) extends Node {

    override def toStr = {
        args_list match {
            case NodeList(list) => name.toStr + "(" + list.map(_.toStr).mkString("", ",", "") + ")"
            case _ => name.toStr + "(" + args_list.toStr + ")"
        }
    }
}

case class FunDef(name: String, formal_args: Node, body: Node) extends Node {
    override def toStr = {
        var str = "\ndef " + name + "(" + formal_args.toStr + "):\n"
        str += body.toStr.replaceAll("(?m)^", indent) + "\n"
        str
    }
}

case class LambdaDef(formal_args: Node, body: Node) extends Node {
    override def toStr = "lambda " + formal_args.toStr + ": " + body.toStr
}

case class ClassDef(name: String, inherit_list: Node, suite: Node) extends Node {
    override def toStr = {
        val str = "\nclass " + name
        var inheritStr = ""
        val suiteStr = ":\n" + suite.toStr.replaceAll("(?m)^", indent)
        inherit_list match {
            case NodeList(x) => if(x.nonEmpty) inheritStr = "(" + x.map(_.toStr).mkString("", ",", "") + ")"
            case _ =>
        }
        str + inheritStr + suiteStr
    }
}

case class NodeList(list: List[Node]) extends Node {
    override def toStr = {
        list.map(_.toStr).mkString("", "\n", "")
    }
}

case class KeyDatumList(list: List[KeyDatum]) extends Node {
    override def toStr = list.map(_.toStr).mkString("{", ",", "}")
}

case class IdList(list: List[Variable]) extends Node {
    override def toStr = list.map(_.toStr).mkString("", ",", "")
}

case class ElemList(list: List[Node]) extends Node {
    override def toStr = list.map(_.toStr).mkString("[", ",", "]")
}

case class Tuple(list: List[Node]) extends Node {
    override def toStr = if(list.isEmpty) "()"
                         else if(list.length==1) "(" + list.head.toStr + ",)"
                         else list.map(_.toStr).mkString("(", ",", ")")
}

case class EmptyReturn() extends Node {
    override def toStr = ""
}
        