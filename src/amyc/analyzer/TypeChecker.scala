package amyc
package analyzer

import utils._
import ast.SymbolicTreeModule._
import ast.Identifier

// The type checker for Amy
// Takes a symbolic program and rejects it if it does not follow the Amy typing rules.
object TypeChecker extends Pipeline[(Program, SymbolTable), (Program, SymbolTable)] {

  def run(ctx: Context)(v: (Program, SymbolTable)): (Program, SymbolTable) = {
    import ctx.reporter._

    val (program, table) = v

    case class Constraint(found: Type, expected: Type, pos: Position)

    // Represents a type variable.
    // It extends Type, but it is meant only for internal type checker use,
    //  since no Amy value can have such type.
    case class TypeVariable private (id: Int) extends Type
    object TypeVariable {
      private val c = new UniqueCounter[Unit]
      def fresh(): TypeVariable = TypeVariable(c.next(()))
    }

    // Generates typing constraints for an expression `e` with a given expected type.
    // The environment `env` contains all currently available bindings (you will have to
    //  extend these, e.g., to account for local variables).
    // Returns a list of constraints among types. These will later be solved via unification.
    def genConstraints(e: Expr, expected: Type)(implicit env: Map[Identifier, Type]): List[Constraint] = {
      
      // This helper returns a list of a single constraint recording the type
      //  that we found (or generated) for the current expression `e`
      def topLevelConstraint(found: Type): List[Constraint] =
        List(Constraint(found, expected, e.position))
      
      e match {
        case IntLiteral(_) =>
          topLevelConstraint(IntType)
        case BooleanLiteral(_) =>
          topLevelConstraint(BooleanType)
        case UnitLiteral() => topLevelConstraint(UnitType)
        case StringLiteral(_) =>
          topLevelConstraint(StringType)
        case Variable(name) => topLevelConstraint(env(name))
        case Sequence(e1,e2) => {
          val e2Type = TypeVariable.fresh
          topLevelConstraint(e2Type) ::: genConstraints(e1, TypeVariable.fresh) ::: genConstraints(e2, e2Type) 
        }
          
        case Equals(lhs, rhs) =>{
          val equtype = TypeVariable.fresh()
          topLevelConstraint(BooleanType) ::: genConstraints(lhs,equtype) ::: genConstraints(rhs,equtype)
        } 
        case Plus(lhs,rhs) => genConstraints(lhs,IntType) ::: genConstraints(rhs,IntType) ::: topLevelConstraint(IntType)
        case Minus(lhs,rhs) =>  genConstraints(lhs,IntType) ::: genConstraints(rhs,IntType) ::: topLevelConstraint(IntType)
        case And(lhs,rhs) => genConstraints(lhs,BooleanType) ::: genConstraints(rhs,BooleanType) ::: topLevelConstraint(BooleanType)
        case Or(lhs,rhs) => genConstraints(lhs,BooleanType) ::: genConstraints(rhs,BooleanType) ::: topLevelConstraint(BooleanType)
        case LessThan(lhs,rhs) => genConstraints(lhs,IntType) ::: genConstraints(rhs,IntType) ::: topLevelConstraint(BooleanType)
        case LessEquals(lhs,rhs) => genConstraints(lhs,IntType) ::: genConstraints(rhs,IntType) ::: topLevelConstraint(BooleanType)
        case Mod(lhs,rhs) => genConstraints(lhs,IntType) ::: genConstraints(rhs,IntType) ::: topLevelConstraint(IntType)
        case Concat(lhs,rhs) => genConstraints(lhs,StringType) ::: genConstraints(rhs,StringType) ::: topLevelConstraint(StringType)
        case Times(lhs,rhs) => genConstraints(lhs,IntType) ::: genConstraints(rhs,IntType) ::: topLevelConstraint(IntType)
        case Div(lhs,rhs) => genConstraints(lhs,IntType) ::: genConstraints(rhs,IntType) ::: topLevelConstraint(IntType)

        case Not(e) => genConstraints(e,BooleanType) ::: topLevelConstraint(BooleanType)
        case Neg(e) => genConstraints(e,IntType) ::: topLevelConstraint(IntType)


        case Ite(cond,tzen,elze) => genConstraints(cond,BooleanType) ::: genConstraints(tzen,expected) ::: genConstraints(elze,expected)
        case Let(df, value, body) => {
          val newType = TypeVariable.fresh
          topLevelConstraint(newType) ::: genConstraints(value,df.tt.tpe) ::: genConstraints(body,newType)(env + (df.name -> df.tt.tpe))
        }

        case Call(qname,args) =>
          (table.getFunction(qname) ,table.getConstructor(qname)) match {
              case (Some(d),None) => {

                val argumentConstraint = (args zip d.argTypes).flatMap(a  => genConstraints(a._1,a._2))
                Constraint(d.retType,expected,e.position) :: argumentConstraint
              }

              case (None,Some(d)) => {
                val argumentConstraint = (args zip d.argTypes).flatMap(a=> genConstraints(a._1,a._2))
                Constraint(ClassType(d.parent),expected,e.position) :: argumentConstraint

              }

              case _ => throw new scala.MatchError(e)
          }
          
          
           
          


          

        case Error(msg) => topLevelConstraint(expected) ::: genConstraints(msg,StringType)
        
        // HINT: Take care to implement the specified Amy semantics
        // TODO
        
        case Match(scrut, cases) =>
          // Returns additional constraints from within the pattern with all bindings
          // from identifiers to types for names bound in the pattern.
          // (This is analogous to `transformPattern` in NameAnalyzer.)
          def handlePattern(pat: Pattern, scrutExpected: Type):
            (List[Constraint], Map[Identifier, Type]) =
          {
            pat match {
              case WildcardPattern() =>(List(),Map())
              case IdPattern(name) => {
                val newType = TypeVariable.fresh
                (List(Constraint(newType,scrutExpected,pat.position)),Map(name -> newType)) 
              }
              
              case LiteralPattern(name) => 
                name match {
                  case IntLiteral(_) => (List(Constraint(IntType,scrutExpected,pat.position)),Map())
                  case StringLiteral(_) => (List(Constraint(StringType, scrutExpected, pat.position)), Map())
                  case BooleanLiteral(_) => (List(Constraint(BooleanType, scrutExpected, pat.position)), Map())
                  case UnitLiteral() => (List(Constraint(UnitType, scrutExpected, pat.position)), Map())


                }
              case CaseClassPattern(constr,args) =>
                val patterns = (args zip table.getConstructor(constr).get.argTypes) map (a => handlePattern(a._1,a._2))
                val unzipped_patterns = patterns.unzip
                (Constraint(ClassType( table.getConstructor(constr).get.parent), scrutExpected, pat.position) :: unzipped_patterns._1.flatten,unzipped_patterns._2.flatMap(_.toList).toMap)




            }
          }

          def handleCase(cse: MatchCase, scrutExpected: Type): List[Constraint] = {
            val (patConstraints, moreEnv) = handlePattern(cse.pat, scrutExpected)
            patConstraints ::: genConstraints(cse.expr,expected)(env ++ moreEnv)
            
          }

          val st = TypeVariable.fresh()
          genConstraints(scrut, st) ++ cases.flatMap(cse => handleCase(cse, st))

          // TODO: Implement the remaining cases
      }
    }


    // Given a list of constraints `constraints`, replace every occurence of type variable
    //  with id `from` by type `to`.
    def subst_*(constraints: List[Constraint], from: Int, to: Type): List[Constraint] = {
      // Do a single substitution.
      def subst(tpe: Type, from: Int, to: Type): Type = {
        tpe match {
          case TypeVariable(`from`) => to
          case other => other
        }
      }

      constraints map { case Constraint(found, expected, pos) =>
        Constraint(subst(found, from, to), subst(expected, from, to), pos)
      }
    }

    // Solve the given set of typing constraints and
    //  call `typeError` if they are not satisfiable.
    // We consider a set of constraints to be satisfiable exactly if they unify.
    def solveConstraints(constraints: List[Constraint]): Unit = {
      constraints match {
        case Nil => ()
        case Constraint(found, expected, pos) :: more =>
         (found,expected ) match {
            case (TypeVariable(v),otherType: TypeVariable) =>
              if(v != otherType.id) {
                  solveConstraints(subst_*(constraints,v,otherType))
              }else{
                  solveConstraints(more) 
              }
           
            case (TypeVariable(v),rest) => solveConstraints(Constraint(expected,found,pos) :: more) 
            case (topLevelCons,TypeVariable(v)) => solveConstraints(subst_*(constraints,v,topLevelCons))
            case (typeA,typeB) => if(typeA == typeB) solveConstraints(more) else { error("Type error",pos); solveConstraints(more)}

            }
      }
          // HINT: You can use the `subst_*` helper above to replace a type variable
          //       by another type in your current set of constraints.
          // TODO
    }
    

    // Putting it all together to type-check each module's functions and main expression.
    program.modules.foreach { mod =>
      // Put function parameters to the symbol table, then typecheck them against the return type
      mod.defs.collect { case FunDef(_, params, retType, body) =>
        val env = params.map{ case ParamDef(name, tt) => name -> tt.tpe }.toMap
        solveConstraints(genConstraints(body, retType.tpe)(env))
      }

      // Type-check expression if present. We allow the result to be of an arbitrary type by
      // passing a fresh (and therefore unconstrained) type variable as the expected type.
      val tv = TypeVariable.fresh()
      mod.optExpr.foreach(e => solveConstraints(genConstraints(e, tv)(Map())))
    }

    v

  }
}


