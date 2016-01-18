package simplifier

import AST._
import scala.math.pow

// to implement
// avoid one huge match of cases
// take into account non-greedy strategies to resolve cases with power laws
object Simplifier {

  def remove(item: Node, list: List[Node]) =
    list diff List(item)

  val evaluations = Map(
    "+" -> ((x: Double, y: Double) => x + y),
    "-" -> ((x: Double, y: Double) => x - y),
    "*" -> ((x: Double, y: Double) => x * y),
    "/" -> ((x: Double, y: Double) => x / y),
    "%" -> ((x: Double, y: Double) => x - y),
    "**" -> ((x: Double, y:Double) => pow(x, y))
  )

  val comparison_negation = Map (
    "==" -> "!=",
    "!=" -> "==",
    "<=" -> ">",
    ">=" -> "<",
    "<" -> ">=",
    ">" -> "<="
  )

  def simplify(node: Node) : Node = {
    node match {

      /** recognize tuples **/
      case BinExpr("+", Tuple(first), Tuple(second)) =>
        var first_simplified = List[Node]()
        var second_simplified = List[Node]()

        for(item <- first) {
          val simplified_item = simplify(item)
          if(!simplified_item.isInstanceOf[EmptyReturn]) {
            first_simplified ++= List(simplified_item)
          }
        }

        for(item <- second) {
          val simplified_item = simplify(item)
          if(!simplified_item.isInstanceOf[EmptyReturn]) {
            second_simplified ++= List(simplified_item)
          }
        }

        Tuple(first_simplified ++ second_simplified)

      /** recognize power laws **/
      case BinExpr("*", first @ BinExpr("**", first_left, first_right), second @ BinExpr("**", second_left, second_right)) =>
        val first_left_simplified = simplify(first_left)
        val second_left_simplified = simplify(second_left)

        if(first_left_simplified.equals(second_left_simplified)) {
          return simplify(BinExpr("**", first_left_simplified, simplify(BinExpr("+", simplify(first_right), simplify(second_right)))))
        }

        BinExpr("*", simplify(first), simplify(second))


      case BinExpr("**", first @ BinExpr("**", first_left, first_right), second) =>
        simplify(BinExpr("**", simplify(first_left), simplify(BinExpr("*", simplify(first_right), simplify(second)))))


      case
        BinExpr("+",
        top_left @ BinExpr(op @ ("+" | "-"),
        BinExpr("**", var1: Variable, int1: IntNum),
        BinExpr("*",
        BinExpr("*", int2: IntNum, var2: Variable),
        var3: Variable)),
        top_right @ BinExpr("**", var4: Variable, int3: IntNum))
      =>

        val var1_simplified = simplify(var1)
        val var2_simplified = simplify(var2)
        val var3_simplified = simplify(var3)
        val var4_simplified = simplify(var4)

        if(int1.equals(int2) && int2.equals(int3) && int1.equals(IntNum(2))) {
          if((var1_simplified.equals(var2_simplified) && var4_simplified.equals(var3_simplified)) ||
            (var1_simplified.equals(var3_simplified) && var4_simplified.equals(var2_simplified))) {
            return simplify(BinExpr("**", simplify(BinExpr(op, var1_simplified, var4_simplified)), IntNum(2)))
          }
        }

        simplify(BinExpr("+", simplify(top_left), simplify(top_right)))


      case
        BinExpr("-",
        top_left @ BinExpr("**",
        BinExpr("+", var1: Variable, var2: Variable),
        int1: IntNum),
        top_right @ BinExpr("**",
        BinExpr("-", var3: Variable, var4: Variable),
        int2: IntNum))
      =>

        val var1_simplified = simplify(var1)
        val var2_simplified = simplify(var2)
        val var3_simplified = simplify(var3)
        val var4_simplified = simplify(var4)

        if(int1.equals(int2) && int1.equals(IntNum(2))) {
          if((var1_simplified.equals(var3_simplified) && var2_simplified.equals(var4_simplified)) ||
            (var1_simplified.equals(var4_simplified) && var2_simplified.equals(var3_simplified))) {
            return simplify(BinExpr("*", simplify(BinExpr("*", IntNum(4), var1_simplified)), var2_simplified))
          }
        }

        simplify(BinExpr("+", simplify(top_left), simplify(top_right)))


      case
        BinExpr("-",
        top_left @ BinExpr("-",
        BinExpr("**",
        BinExpr("+", var1: Variable, var2: Variable),
        int1: IntNum),
        BinExpr("**", var3: Variable, int2: IntNum)),
        top_right @ BinExpr("*",
        BinExpr("*", int3: IntNum, var4: Variable),
        var5: Variable))
      =>

        val var1_simplified = simplify(var1)
        val var2_simplified = simplify(var2)
        val var3_simplified = simplify(var3)
        val var4_simplified = simplify(var4)
        val var5_simplified = simplify(var5)

        if(int1.equals(int2) && int1.equals(int3) && int1.equals(IntNum(2))) {
          if((var1_simplified.equals(var4_simplified) && var2_simplified.equals(var5_simplified)) ||
            (var1_simplified.equals(var5_simplified) && var2_simplified.equals(var4_simplified))) {
            if(var1_simplified.equals(var3_simplified)) {
              return simplify(BinExpr("**", var2_simplified, IntNum(2)))
            }
            else if(var2_simplified.equals(var3_simplified)) {
              return simplify(BinExpr("**", var1_simplified, IntNum(2)))
            }
          }
        }

        simplify(BinExpr("-", simplify(top_left), simplify(top_right)))

      /** remove duplicate keys **/
      case KeyDatumList(list) =>
        var simplified = Map[Node, KeyDatum]()
        for(item <- list) {
          simplified += simplify(item.key) -> item
        }

        var simplified_asList = List[KeyDatum]()
        simplified.values.foreach(value =>
          simplified_asList ++= List(value)
        )

        KeyDatumList(simplified_asList)

      /** concatenate lists **/
      case BinExpr("+", ElemList(first), ElemList(second)) =>
        var first_simplified = List[Node]()
        var second_simplified = List[Node]()

        for(item <- first) {
          val simplified_item = simplify(item)
          if(!simplified_item.isInstanceOf[EmptyReturn]) {
            first_simplified ++= List(simplified_item)
          }
        }

        for(item <- second) {
          val simplified_item = simplify(item)
          if(!simplified_item.isInstanceOf[EmptyReturn]) {
            second_simplified ++= List(simplified_item)
          }
        }

        ElemList(first_simplified ++ second_simplified)



      /** understand distributive property of multiplication **/
      case BinExpr(op @ ("+" | "-"), left @ BinExpr("*", var1, var2), right @ BinExpr("*", var3, var4)) =>
        val var1_simplified = simplify(var1)
        val var2_simplified = simplify(var2)
        val var3_simplified = simplify(var3)
        val var4_simplified = simplify(var4)

        if(var1_simplified.equals(var3_simplified)) {
          return BinExpr("*", var1_simplified, simplify(BinExpr(op, var2_simplified, var4_simplified)))
        }
        if(var2_simplified.equals(var4_simplified)) {
          return BinExpr("*", simplify(BinExpr(op, var1_simplified, var3_simplified)), var2_simplified)
        }

        BinExpr(op, simplify(left), simplify(right))

      case BinExpr(
      "+",
      first @ BinExpr("+", left_first @ _, right_first @ BinExpr("*", var1: Variable, var2: Variable)),
      second @ BinExpr("*", var3: Variable, var4: Variable)) =>
        simplify(BinExpr("+", simplify(left_first), simplify(BinExpr("+", right_first, second))))

      case BinExpr(op @ ("+" | "-"), left @ BinExpr("*", IntNum(n), var1), right) =>
        val var1_simplified = simplify(var1)
        val right_simplified = simplify(right)

        if(var1_simplified.equals(right_simplified)) {
          val coefficient = evaluations(op).apply(n.toDouble, 1).toInt
          return if(coefficient != 1) BinExpr("*", IntNum(coefficient), var1_simplified) else var1_simplified
        }
        BinExpr(op, simplify(left), simplify(right))

      case BinExpr(op @ ("+" | "-"), left @ BinExpr("*", FloatNum(n), var1), right) =>
        val var1_simplified = simplify(var1)
        val right_simplified = simplify(right)

        if(var1_simplified.equals(right_simplified)) {
          val coefficient = evaluations(op).apply(n, 1)
          return if(coefficient != 1) BinExpr("*", FloatNum(coefficient), var1_simplified) else var1_simplified
        }
        BinExpr(op, simplify(left), simplify(right))

      /** understand commutativity **/
      case BinExpr("-", BinExpr(op @ ("+" | "-"), left, right), variable @ Variable(name)) =>
        simplify(BinExpr(op, BinExpr("-", left, variable), right))

      /**
       * evaluate constants
       * simplify division
       * simplify expressions
       **/

      case BinExpr("+", left: IntNum, right: Variable) =>
        if(left.equals(IntNum(0))) {
          return simplify(right)
        }

        BinExpr("+", simplify(right), simplify(left))


      case BinExpr("+", left: Variable, right: IntNum) =>
        if(right.equals(IntNum(0))) {
          return simplify(left)
        }

        BinExpr("+", simplify(left), simplify(right))


      case BinExpr("*", left: IntNum, right: Variable) =>
        if(left.equals(IntNum(0))) {
          return IntNum(0)
        }
        if(left.equals(IntNum(1))) {
          return simplify(right)
        }

        BinExpr("*", simplify(left), simplify(right))


      case BinExpr("*", left: Variable, right: IntNum) =>
        if(right.equals(IntNum(0))) {
          return IntNum(0)
        }
        if(right.equals(IntNum(1))) {
          return simplify(left)
        }

        BinExpr("*", simplify(left), simplify(right))


      case BinExpr("or", b @ _, c @ _) =>
        var left = simplify(b)
        var right = simplify(c)

        if(left.equals(right)) {
          return left
        }
        if(left.equals(TrueConst()) || right.equals(TrueConst())) {
          return TrueConst()
        }
        if(left.equals(FalseConst())) {
          return right
        }
        if(right.equals(FalseConst())) {
          return left
        }
        if(left.toStr.compareToIgnoreCase(right.toStr) > 0) {
          val temp = left
          left = right
          right = temp
        }

        BinExpr("or", left, right)


      case BinExpr("and", b @ _, c @ _) =>
        var left = simplify(b)
        var right = simplify(c)

        if(left.equals(right)) {
          return left
        }
        if(left.equals(FalseConst()) || right.equals(FalseConst())) {
          return FalseConst()
        }
        if(left.equals(TrueConst())) {
          return right
        }
        if(right.equals(TrueConst())) {
          return left
        }
        if(left.toStr.compareToIgnoreCase(right.toStr) > 0) {
          val temp = left
          left = right
          right = temp
        }

        BinExpr("and", left, right)


      case BinExpr(op @ ("==" | ">=" | "<="), b @ _, c @ _) =>
        val left = simplify(b)
        val right = simplify(c)
        if(left.equals(right)) {
          return TrueConst()
        }

        BinExpr(op, left, right)


      case BinExpr(op @ ("!=" | ">" | "<"), b @ _, c @ _) =>
        val left = simplify(b)
        val right = simplify(c)
        if(left.equals(right)) {
          return FalseConst()
        }

        BinExpr(op, left, right)


      case BinExpr("+", a: Variable, b: Unary) =>
        val left = simplify(a)
        val right = simplify(b)
        if(b.op == "-" && left.equals(simplify(b.expr))) {
          return IntNum(0)
        }

        BinExpr("+", right, left)


      case BinExpr("+", a: Unary, b: Variable) =>
        val left = simplify(a)
        val right = simplify(b)
        if(a.op == "-" && right.equals(simplify(a.expr))) {
          return IntNum(0)
        }

        BinExpr("+", left, right)


      case BinExpr(a @ _, b @ _, c @ _) =>
        var left = simplify(b)
        var right = simplify(c)

        a match {
          //WARN: This case must occur before changing the symmetry of "+" and "*".
          case "*" =>
            right match {
              case BinExpr("/", b : IntNum, c @ _) =>
                if(b.equals(IntNum(1))) {
                  return BinExpr("/", left, simplify(c))
                }

              case _ =>
            }

          case "+" | "*"  =>
            if(right.toStr.compareToIgnoreCase(left.toStr) < 0) {
              val temp = left
              left = right
              right = temp
            }

          case "-" =>
            if(left.equals(right)) {
              return IntNum(0)
            }

          case "/" =>
            if(left.equals(right)) {
              return IntNum(1)
            }

            if(left.equals(IntNum(1))) {
              right match {
                case BinExpr("/", num : IntNum, denominator @ _) =>
                  if(num.equals(IntNum(1)))
                    return simplify(denominator)

                case _ =>
              }
            }

          case "**" =>
            if(right.equals(IntNum(0)) || right.equals(FloatNum(0))) {
              return IntNum(1)
            }
            if(right.equals(IntNum(1)) || right.equals(FloatNum(1))) {
              return left
            }


          case _ =>
        }

        left match {
          case IntNum(n) =>
            right match {
              case IntNum(m) =>
                IntNum(evaluations(a).apply(n.toDouble, m.toDouble).toInt)

              case FloatNum(m) =>
                FloatNum(evaluations(a).apply(n.toDouble, m))

              case Variable(name) =>
                BinExpr(a, left, right)

              case BinExpr(_, _, _) =>
                BinExpr(a, left, right)
            }

          case FloatNum(n) =>
            right match {
              case IntNum(m) =>
                FloatNum(evaluations(a).apply(n, m.toDouble))

              case FloatNum(m) =>
                FloatNum(evaluations(a).apply(n, m))

              case Variable(name) =>
                BinExpr(a, left, right)

              case BinExpr(_, _, _) =>
                BinExpr(a, left, right)
            }

          case Variable(name) =>
            BinExpr(a, left, right)

          case BinExpr(_, _, _) =>
            BinExpr(a, left, right)
        }


      case Unary("not", FalseConst()) =>
        TrueConst()


      case Unary("not", TrueConst()) =>
        FalseConst()

      /** cancel double unary ops **/
      case Unary("not", Unary("not", right)) =>
        simplify(right)

      case Unary("-", Unary("-", right)) =>
        simplify(right)

      /** get rid of not before comparisons **/
      case Unary("not", BinExpr(op @ ("==" | "!=" | ">" | "<" | ">=" | "<="), left, right)) =>
        BinExpr(comparison_negation(op), simplify(left), simplify(right))

      /** remove no effect instructions **/
      case Assignment(left, right) =>
        if(left.equals(right)) {
          return EmptyReturn()
        }
        Assignment(simplify(left), simplify(right))

      /** simplify if-else instruction with known condition **/
      case IfElifElseInstruction(ConditionalSuite(TrueConst(), NodeList(list)), List(), _) =>
        simplify(list.head)

      case IfElifElseInstruction(ConditionalSuite(TrueConst(), trueInstr), List(), _) =>
        simplify(trueInstr)

      case IfElifElseInstruction(ConditionalSuite(FalseConst(), _), List(), Some(NodeList(list))) =>
        simplify(list.head)

      case IfElifElseInstruction(ConditionalSuite(FalseConst(), _), List(), Some(falseInstr)) =>
        simplify(falseInstr)

      /** simplify if-else expression with known condition **/
      case IfElseExpr(TrueConst(), true_instr @ _, _) =>
        simplify(true_instr)

      case IfElseExpr(FalseConst(), _, false_instr @ _) =>
        simplify(false_instr)

      /** remove while loop with False condition **/
      case WhileInstr(condition, body) =>
        if(simplify(condition).equals(FalseConst())) {
          return EmptyReturn()
        }
        WhileInstr(simplify(condition), simplify(body))

      /** decompose **/
      case NodeList(list) =>
        var simplified_list = List[Node]()

        /** remove dead assignments **/
        var cleaned_list = list
        for(slide <- list.iterator.sliding(2)) {
          if(slide.length == 2) {
            (slide.head, slide(1)) match {
              case(first @ NodeList(List(Assignment(head_left, head_right))), NodeList(List(Assignment(tail_left, tail_right)))) =>
                if(simplify(head_left).equals(simplify(tail_left))) {
                  cleaned_list = remove(first, cleaned_list)
                }

              case _ =>
            }
          }
        }

        for(item <- cleaned_list) {
        }

        for(item <- cleaned_list) {
          item match {
            /** remove dead assignments **/
            case NodeList(list @ List(Assignment(first_left, first_right), second @ Assignment(second_left, second_right))) =>
              if(simplify(first_left).equals(simplify(second_left))) {
                simplified_list ++= List(NodeList(List(simplify(second))))
                return NodeList(simplified_list)
              }

            case _ =>
          }

          val simplified_item = simplify(item)
          if(!simplified_item.isInstanceOf[EmptyReturn]) {
            simplified_list ++= List(simplified_item)
          }
        }

        if(simplified_list.nonEmpty){
          return NodeList(simplified_list)
        }

        EmptyReturn()


      case _ =>
        simplify _
        node
    }
  }

}
