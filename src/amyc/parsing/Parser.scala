package amyc
package parsing

import scala.language.implicitConversions

import amyc.ast.NominalTreeModule._
import amyc.utils._
import Tokens._
import TokenKinds._

import scallion.syntactic._

// The parser for Amy
object Parser extends Pipeline[Iterator[Token], Program]
                 with Syntaxes[Token, TokenKind] with Debug[Token, TokenKind]
                 with Operators {
  import Implicits._

  override def getKind(token: Token): TokenKind = TokenKind.of(token)

  val eof: Syntax[Token] = elem(EOFKind)
  def op(string: String): Syntax[String] = accept(OperatorKind(string)) { case OperatorToken(name) => name }
  def kw(string: String): Syntax[Token] = elem(KeywordKind(string))

  implicit def delimiter(string: String): Syntax[Token] = elem(DelimiterKind(string))

  // An entire program (the starting rule for any Amy file).
  lazy val program: Syntax[Program] = many1(many1(module) ~<~ eof).map(ms => Program(ms.flatten.toList).setPos(ms.head.head))

  // A module (i.e., a collection of definitions and an initializer expression)
  lazy val module: Syntax[ModuleDef] = (kw("object") ~ identifier ~ "{" ~ many(definition) ~ opt(expr) ~ "}").map {
    case obj ~ id ~ _ ~ defs ~ body ~ _ => ModuleDef(id, defs.toList, body).setPos(obj)
  }

  // An identifier.
  val identifier: Syntax[String] = accept(IdentifierKind) {
    case IdentifierToken(name) => name
  }

  // An identifier along with its position.
  val identifierPos: Syntax[(String, Position)] = accept(IdentifierKind) {
    case id@IdentifierToken(name) => (name, id.position)
  }

  // A definition within a module.
  lazy val definition: Syntax[ClassOrFunDef] = abstractClass.up[ClassOrFunDef] | 
    caseClass.up[ClassOrFunDef] | function.up[ClassOrFunDef] //

  lazy val abstractClass: Syntax[AbstractClassDef] = (kw("abstract") ~ kw("class") ~ identifier).map {
    case abs ~ _ ~ id => AbstractClassDef(id).setPos(abs)
  }

  lazy val caseClass: Syntax[CaseClassDef] = (kw("case") ~ kw("class") ~ identifier ~ 
      "(" ~ (parameters | noParameters) ~ ")" ~ kw("extends") ~ identifier).map {
      case c ~ _ ~ id ~ _ ~ params ~ _ ~ _ ~ parent => CaseClassDef(id, params, parent).setPos(c)
    }

  lazy val function: Syntax[FunDef] = (kw("def") ~ identifier ~ "(" ~ (parameters | noParameters) ~ ")" ~
      ":" ~ typeTree ~ "=" ~ "{" ~ expr ~ "}").map {
      case d ~ id ~ _ ~ params ~ _ ~ _ ~ t ~ _ ~ _ ~ body ~ _ => FunDef(id, params, t, body).setPos(d)
    }

  // A list of parameter definitions.
  lazy val parameters: Syntax[List[ParamDef]] = recursive {
    (parameter ~ opt(comaThenParameters | valueThenParameters)).map{
      case p ~ None => List(p)
      case p ~ Some((optValue, dp)) => ParamDef(p.name, p.tt, optValue) :: dp
    }}
  
  lazy val comaThenParameters: Syntax[(Option[Expr], List[ParamDef])] = recursive {("," ~ parameter  ~ opt(comaThenParameters | valueThenParameters)).map{
    case _ ~ p ~ None => (None, List(p))
    case _ ~ p ~ Some((optValue, dp)) => (None, ParamDef(p.name, p.tt, optValue) :: dp)
  }}
  
  val noParameters: Syntax[List[ParamDef]] = epsilon(Nil)

  lazy val valueThenParameters: Syntax[(Option[Expr], List[ParamDef])] = ("=" ~ expr ~ opt("," ~ defaultParameters)).map{
    case _ ~ value ~ Some(_ ~ dp) => (Some(value), dp)
    case _ ~ value ~ None => (Some(value), Nil)
  }

  lazy val defaultParameters: Syntax[List[ParamDef]] = repsep(defaultParameter, ",").map(_.toList)

  lazy val defaultParameter: Syntax[ParamDef] = (identifierPos ~ ":" ~ typeTree ~ "=" ~ expr).map {
    case id ~ _ ~ t ~ _ ~ value => ParamDef(id._1, t, Some(value))  
  }

  // A parameter definition, i.e., an identifier along with the expected type.
  lazy val parameter: Syntax[ParamDef] = (identifierPos ~ ":" ~ typeTree).map {
    case id ~ _ ~ t => ParamDef(id._1, t, None).setPos(id._2)
  }



  // A type expression.
  lazy val typeTree: Syntax[TypeTree] = primitiveType | identifierType

  // A built-in type (such as `Int`).
  val primitiveType: Syntax[TypeTree] = accept(PrimTypeKind) {
    case tk@PrimTypeToken(name) => TypeTree(name match {
      case "Unit" => UnitType
      case "Boolean" => BooleanType
      case "Int" => IntType
      case "String" => StringType
      case _ => throw new java.lang.Error("Unexpected primitive type name: " + name)
    }).setPos(tk)
  }

  // A user-defined type (such as `List`).
  lazy val identifierType: Syntax[TypeTree] = (identifierPos ~ opt("." ~>~ identifier)).map {
    case id ~ Some(id2) => TypeTree(ClassType(QualifiedName(Some(id._1), id2))).setPos(id._2)
    case id ~ None => TypeTree(ClassType(QualifiedName(None, id._1))).setPos(id._2)
  }


  // An expression.
  // HINT: You can use `operators` to take care of associativity and precedence
  lazy val expr: Syntax[Expr] = recursive {
    sequence | let.up[Expr]
  }

  lazy val sequence: Syntax[Expr] = (ifMatchExpr ~ opt(";" ~>~ expr)).map {
      case e1 ~ Some(e2) => Sequence(e1, e2).setPos(e1)
      case e ~ None => e
    }
  

  lazy val let: Syntax[Let] =
    (kw("val") ~ parameter ~ "=" ~ ifMatchExpr ~ ";" ~ expr).map {
      case pos ~ df ~ _ ~ value ~ _ ~ body => Let(df, value, body).setPos(pos)
    }
  

  lazy val ifMatchExpr: Syntax[Expr] = ite | matchExpr
  

  lazy val ite: Syntax[Expr] =
    (kw("if") ~ "(" ~ binOpExpr ~ ")" ~ "{" ~ expr ~ "}" ~
      kw("else").skip ~ "{" ~ expr ~ "}").map {
        case pos ~ _ ~ cond ~ _ ~ _ ~ thenn ~ _ ~ _ ~ elze ~ _ => Ite(cond, thenn, elze).setPos(pos)
      }
  

  lazy val matchExpr: Syntax[Expr] =
    (binOpExpr ~ opt(kw("match").skip ~ "{" ~ many1(matchCase) ~ "}")).map {
      case e ~ None => e
      case e ~ Some(_ ~ cases ~ _) => Match(e, cases.toList).setPos(e)
    }
  

  lazy val matchCase: Syntax[MatchCase] =
    (kw("case") ~ pattern ~ "=>" ~ expr).map {
      case pos ~ pat ~ _ ~ e => MatchCase(pat, e).setPos(pos)
    }
  


  val plus = op("+")
  val minus = op("-")
  val times = op("*")
  val div = op("/")
  val mod = op("%")
  val lessThan = op("<")
  val lessEquals = op("<=")
  val and = op("&&")
  val or = op("||")
  val equals = op("==")
  val concat = op("++")
  val neg = op("!")

  lazy val binOpExpr: Syntax[Expr] = 
    operators(unaryOpExpr)(
      times | div | mod is LeftAssociative,
      plus | minus | concat is LeftAssociative,
      lessThan | lessEquals is LeftAssociative,
      equals is LeftAssociative,
      and is LeftAssociative,
      or is LeftAssociative
    ) {
        case (l, "+", r) => Plus(l,r).setPos(l)
        case (l, "-", r) => Minus(l,r).setPos(l)
        case (l, "*", r) => Times(l,r).setPos(l)
        case (l, "/", r) => Div(l,r).setPos(l)
        case (l, "%", r) => Mod(l,r).setPos(l)
        case (l, "<", r) => LessThan(l,r).setPos(l)
        case (l, "<=", r) => LessEquals(l,r).setPos(l)
        case (l, "&&", r) => And(l,r).setPos(l)
        case (l, "||", r) => Or(l,r).setPos(l)
        case (l, "==", r) => Equals(l,r).setPos(l)
        case (l, "++", r) => Concat(l,r).setPos(l)
        case (_, o, _) => throw new java.lang.Error("Unexpected operator: " + o)
      }
  

  lazy val unaryOpExpr: Syntax[Expr] = (opt(neg | minus) ~ simpleExpr).map {
    case None ~ e => e
    case Some(o) ~ e => o match {
      case "!" => Not(e).setPos(e)
      case "-" => Neg(e).setPos(e)
    }
  }

  // A literal expression.
  lazy val literal: Syntax[Literal[_]] =  notUnitLiteral 

  val notUnitLiteral: Syntax[Literal[_]] = accept(LiteralKind) {
    case BoolLitToken(v) => BooleanLiteral(v)
    case IntLitToken(v) => IntLiteral(v)
    case StringLitToken(v) => StringLiteral(v)
  }

  // A pattern as part of a mach case.
  lazy val pattern: Syntax[Pattern] = recursive {
    literalPattern.up[Pattern] | wildPattern.up[Pattern] | idOrCaseClassPattern.up[Pattern]
  }

  lazy val literalPattern: Syntax[LiteralPattern[_]] = (literal | unitLiteral.up[Literal[_]]).map {
    case l => LiteralPattern(l).setPos(l)
  }

  lazy val unitLiteral: Syntax[UnitLiteral] = ("(" ~ ")").map {
    case open ~ _ => UnitLiteral().setPos(open)
  }

  val wildPattern: Syntax[WildcardPattern] = kw("_").map {
    case u => WildcardPattern().setPos(u)
  }

  lazy val idOrCaseClassPattern: Syntax[Pattern] =
    (identifierPos ~ opt(opt("." ~>~ identifier) ~ 
        "(" ~ patterns ~ ")")).map {
        case id ~ None => IdPattern(id._1).setPos(id._2)
        case id ~ Some(None ~ _ ~ pats ~ _) => CaseClassPattern(QualifiedName(None, id._1), pats).setPos(id._2)
        case id ~ Some(Some(id2) ~ _ ~ pats ~ _) => CaseClassPattern(QualifiedName(Some(id._1), id2), pats).setPos(id._2)
      }

  lazy val patterns: Syntax[List[Pattern]] = repsep(pattern, ",").map(_.toList)
  


  // HINT: It is useful to have a restricted set of expressions that don't include any more operators on the outer level.
  lazy val simpleExpr: Syntax[Expr] = literal.up[Expr] | variableOrCall | error.up[Expr] | 
    parenthesis

  lazy val parenthesis: Syntax[Expr] = ("(" ~ opt(expr) ~ ")").map {
    case open ~ None ~ _ => UnitLiteral().setPos(open)
    case _ ~ Some(e) ~ _ => e
  }

  lazy val variableOrCall: Syntax[Expr] =
    (identifierPos ~ opt(opt("." ~>~ identifier) ~ "(" ~ (args|noArgs) ~ ")")).map {
        case id ~ None => Variable(id._1).setPos(id._2)
        case id ~ Some(None ~ _ ~ a ~ _) => Call(QualifiedName(None, id._1), a).setPos(id._2)
        case id ~ Some(Some(id2) ~ _ ~ a  ~ _) => Call(QualifiedName(Some(id._1), id2), a).setPos(id._2)
      }

  lazy val args: Syntax[List[(Option[Name],Expr)]] = 
    (expr ~ opt(comaThenArgs | valueThenArgs)).map{
      case Variable(id) ~ Some((Some(v), da)) => (Some(id), v) :: da
      case e ~ None => List((None, e))
      case e ~ Some((None, da)) => (None, e) :: da
      case e ~ Some((Some(_), _)) => throw new java.lang.Error("Invalid name for argument, must be an identifier")
    }

  lazy val comaThenArgs: Syntax[(Option[Expr], List[(Option[Name],Expr)])] = recursive {
    ("," ~ expr ~ opt(comaThenArgs | valueThenArgs)).map{
      case _ ~ Variable(id) ~ Some((Some(v), da)) => (None, (Some(id), v) :: da)
      case _ ~ e ~ None => (None, List((None, e)))
      case _ ~ e ~ Some((None, da)) => (None, (None, e) :: da)
      case _ ~ e ~ Some((Some(_), _)) => throw new java.lang.Error("Invalid name for argument, must be an identifier")
    }}

  val noArgs: Syntax[List[(Option[Name],Expr)]] = epsilon(Nil)

  lazy val valueThenArgs: Syntax[(Option[Expr], List[(Option[Name],Expr)])] = ("=" ~ expr ~ opt("," ~ defaultArgs)).map{
    case _ ~ value ~ Some(_ ~ da) => (Some(value), da)
    case _ ~ value ~ None => (Some(value), Nil)
  }

  lazy val defaultArgs: Syntax[List[(Option[Name],Expr)]] = repsep(defaultArg, ",").map(_.toList)

  lazy val defaultArg: Syntax[(Option[Name], Expr)] = (identifier ~ "=" ~ expr).map {
    case id ~ _ ~ value => (Some(id), value)
  }
  

  lazy val error: Syntax[Error] =
    (kw("error") ~ "(" ~ expr ~ ")").map {
      case pos ~ _ ~ e ~ _ => Error(e).setPos(pos)
  }


  // Ensures the grammar is in LL(1), otherwise prints some counterexamples
  lazy val checkLL1: Boolean = {
    
    if (program.isLL1) {
      true
    } else {
      debug(program)
      false
    }
  }

  override def run(ctx: Context)(tokens: Iterator[Token]): Program = {
    import ctx.reporter._
    if (!checkLL1) {
      ctx.reporter.fatal("Program grammar is not LL1!")
    }

    program(tokens) match {
      case Parsed(result, rest) => result
      case UnexpectedEnd(rest) => fatal("Unexpected end of input.")
      case UnexpectedToken(token, rest) => fatal("Unexpected token: " + token + ", possible kinds: " + rest.first.map(_.toString).mkString(", "))
    }
  }
}
