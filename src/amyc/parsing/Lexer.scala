package amyc
package parsing

import utils._
import java.io.File

import scallion.lexical._
import scallion.input._

import amyc.utils.Position

// The lexer for Amy.
object Lexer extends Pipeline[List[File], Iterator[Token]]
                with Lexers[Token, Char, SourcePosition] {

  /** Tiny Scallion-lexer reference:
    * ==============================
    * Scallion's lexer essentially allows you to define a list of regular expressions
    * in their order of priority. To tokenize a given input stream of characters, each
    * individual regular expression is applied in turn. If a given expression matches, it
    * is used to produce a token of maximal length. Whenever a regular expression does not
    * match, the expression of next-highest priority is tried.
    * The result is a stream of tokens.
    *
    * Regular expressions `r` can be built using the following operators:
    *   - `word("abc")`  matches the sequence "abc" exactly
    *   - `r1 | r2`      matches either expression `r1` or expression `r2`
    *   - `r1 ~ r2`      matches `r1` followed by `r2`
    *   - `oneOf("xy")`  matches either "x" or "y"
    *                    (i.e., it is a shorthand of `word` and `|` for single characters)
    *   - `elem(c)`      matches character `c`
    *   - `elem(f)`      matches any character for which the boolean predicate `f` holds 
    *   - `opt(r)`       matches `r` or nothing at all
    *   - `many(r)`      matches any number of repetitions of `r` (including none at all)
    *   - `many1(r)`     matches any non-zero number of repetitions of `r`
    *  
    * To define the token that should be output for a given expression, one can use
    * the `|>` combinator with an expression on the left-hand side and a function
    * producing the token on the right. The function is given the sequence of matched
    * characters and the source-position range as arguments.
    * 
    * For instance,
    *
    *   `elem(_.isDigit) ~ word("kg") |> {
    *     (cs, range) => WeightLiteralToken(cs.mkString).setPos(range._1)) }`
    *
    * will match a single digit followed by the characters "kg" and turn them into a
    * "WeightLiteralToken" whose value will be the full string matched (e.g. "1kg").
    */


  import Tokens._

  val lexer = Lexer(
    // Keywords
    word("abstract") | word("case") | word("class") |
    word("def") | word("else") | word("extends") |
    word("if") | word("match") | word("object") |
    word("val") | word("error") | word("_")
      |> { (cs, range) => KeywordToken(cs.mkString).setPos(range._1) },

    // Primitive type names
    word("Int") | word("String") | word("Boolean") |
    word("Unit")
      |> { (cs, range) => PrimTypeToken(cs.mkString).setPos(range._1) },

    // Boolean literals
    word("true")
      |> { (cs, range) => BoolLitToken(true).setPos(range._1) },
    word("false")
      |> { (cs, range) => BoolLitToken(false).setPos(range._1) },

    // Operators
    word("+") | word("-") | word("*") | word("/") |
    word("%") | word("<") | word("<=") | word("&&") |
    word("||") | word("==") | word("++") | word("!")
      |> { (cs, range) => OperatorToken(cs.mkString).setPos(range._1) },

    // Identifiers
    elem(_.isLetter) ~ many(elem(e => e.isLetter || e.isDigit || e == '_'))
      |> { (cs, range) => IdentifierToken(cs.mkString).setPos(range._1) },

    // Integer literals
    many1(elem(_.isDigit))
      |> { (cs, range) => if (BigInt(cs.mkString).isValidInt)
        IntLitToken(cs.mkString.toInt).setPos(range._1) else
          ErrorToken(s"${cs.mkString} is not a valid integer @${range._1}") },
    // NOTE: Make sure to handle invalid (e.g. overflowing) integer values safely by
    //       emitting an ErrorToken instead.

    // String literals
    elem('"') ~ many(elem(e => e != '\n' && e != '"')) ~ elem('"')
      |> { (cs, range) => StringLitToken(cs.mkString.substring(1,cs.mkString.length - 1)).setPos(range._1) },

    // Delimiters and whitespace
    oneOf(".,:;(){}[]=") | word("=>")
      |> { (cs, range) => DelimiterToken(cs.mkString).setPos(range._1) },
    elem(_.isWhitespace)
      |> { (cs, range) => SpaceToken() },

    // Single line comments
    word("//") ~ many(elem(_ != '\n'))
      |> { cs => CommentToken(cs.mkString("")) },

    // Multiline comments
    // NOTE: Amy does not support nested multi-line comments (e.g. `/* foo /* bar */ */`).
    //       Make sure that unclosed multi-line comments result in an ErrorToken.
    word("/*") ~ many(elem(_ != '*') | (elem('*') ~ elem(_!= '/'))) ~ many1(elem('*')) ~ elem('/')
      |> { cs => CommentToken(cs.mkString("")) },
    word("/*") ~ many(elem(_ != '*') |( elem('*') ~ elem(_ != '/')))
      |> { (cs, range) => ErrorToken(s"Comment not closed @${range._1}").setPos(range._1) }
  ) onError {
    // We also emit ErrorTokens for Scallion-handled errors.
    (cs, range) => ErrorToken(cs.mkString).setPos(range._1)
  } onEnd {
    // Once all the input has been consumed, we emit one EOFToken.
    pos => EOFToken().setPos(pos)
  }

  override def run(ctx: Context)(files: List[File]): Iterator[Token] = {
    var it = Seq[Token]().toIterator

    for (file <- files) {
      val source = Source.fromFile(file, SourcePositioner(file))
      it ++= lexer.spawn(source).filter {
        token =>
          // Remove all whitespace and comment tokens
          token match {
            case SpaceToken() => false
            case CommentToken(_) => false
            case _  => true
          }
      }.map {
        case token@ErrorToken(error) => ctx.reporter.fatal("Unknown token at " + token.position + ": " + error)
        case token => token
      }
    }
    it
  }
}

/** Extracts all tokens from input and displays them */
object DisplayTokens extends Pipeline[Iterator[Token], Unit] {
  override def run(ctx: Context)(tokens: Iterator[Token]): Unit = {
    tokens.foreach(println(_))
  }
}
