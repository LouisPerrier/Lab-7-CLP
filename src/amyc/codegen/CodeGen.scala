package amyc
package codegen

import analyzer._
import ast.Identifier
import ast.SymbolicTreeModule.{Call => AmyCall, Div => AmyDiv, And => AmyAnd, Or => AmyOr, _}
import utils.{Context, Pipeline}
import wasm._
import Instructions._
import Utils._

// Generates WebAssembly code for an Amy program
object CodeGen extends Pipeline[(Program, SymbolTable), Module] {
  def run(ctx: Context)(v: (Program, SymbolTable)): Module = {
    val (program, table) = v

    // Generate code for an Amy module
    def cgModule(moduleDef: ModuleDef): List[Function] = {
      val ModuleDef(name, defs, optExpr) = moduleDef
      // Generate code for all functions
      defs.collect { case fd: FunDef if !builtInFunctions(fullName(name, fd.name)) =>
        cgFunction(fd, name, false)
      } ++
      // Generate code for the "main" function, which contains the module expression
      optExpr.toList.map { expr =>
        val mainFd = FunDef(Identifier.fresh("main"), Nil, TypeTree(IntType), expr)
        cgFunction(mainFd, name, true)
      }
    }

    // Generate code for a function in module 'owner'
    def cgFunction(fd: FunDef, owner: Identifier, isMain: Boolean): Function = {
      // Note: We create the wasm function name from a combination of
      // module and function name, since we put everything in the same wasm module.
      val name = fullName(owner, fd.name)
      Function(name, fd.params.size, isMain){ lh =>
        val locals = fd.paramNames.zipWithIndex.toMap
        val body = cgExpr(fd.body)(locals, lh)
        if (isMain) {
          body <:> Drop // Main functions do not return a value,
                        // so we need to drop the value generated by their body
        } else {
          body
        }
      }
    }

    // Generate code for an expression expr.
    // Additional arguments are a mapping from identifiers (parameters and variables) to
    // their index in the wasm local variables, and a LocalsHandler which will generate
    // fresh local slots as required.
    def cgExpr(expr: Expr)(implicit locals: Map[Identifier, Int], lh: LocalsHandler): Code = {
      expr match {
        case Variable(name) => GetLocal(locals(name))

        case IntLiteral(value) => Const(value)
        case BooleanLiteral(value) => if (value) Const(1) else Const(0)
        case StringLiteral(value) => mkString(value)
        case UnitLiteral() => Const(0)

        case Plus(lhs, rhs) => cgExpr(lhs) <:> cgExpr(rhs) <:> Add
        case Minus(lhs, rhs) => cgExpr(lhs) <:> cgExpr(rhs) <:> Sub
        case Times(lhs, rhs) => cgExpr(lhs) <:> cgExpr(rhs) <:> Mul
        case AmyDiv(lhs, rhs) => cgExpr(lhs) <:> cgExpr(rhs) <:> Div
        case Mod(lhs, rhs) => cgExpr(lhs) <:> cgExpr(rhs) <:> Rem
        case LessThan(lhs, rhs) => cgExpr(lhs) <:> cgExpr(rhs) <:> Lt_s
        case LessEquals(lhs, rhs) => cgExpr(lhs) <:> cgExpr(rhs) <:> Le_s
        case AmyAnd(lhs, rhs) => cgExpr(lhs) <:> 
          If_i32 <:> cgExpr(rhs) <:> 
          Else <:> Const(0) <:> 
          End
        case AmyOr(lhs, rhs) => cgExpr(lhs) <:> 
          If_i32 <:> Const(1) <:> 
          Else <:> cgExpr(rhs) <:> 
          End
        case Equals(lhs, rhs) => cgExpr(lhs) <:> cgExpr(rhs) <:> Eq
        case Concat(lhs, rhs) => cgExpr(lhs) <:> cgExpr(rhs) <:> Call(concatImpl.name)

        case Not(e) => cgExpr(e) <:> Eqz
        case Neg(e) => Const(0) <:> cgExpr(e) <:> Sub
        
        case AmyCall(qname, args) =>
          val cgArgs = args.map(cgExpr(_))
          table.getConstructor(qname) match {

            case Some(constructor) => 
              val address = lh.getFreshLocal()
              val argCodes: List[Code] = cgArgs.zipWithIndex.map{ 
                case (cgArg, idx) =>
                  GetLocal(address) <:> Const(4*(idx+1)) <:> Add <:> cgArg <:> Store
              }
              GetGlobal(Utils.memoryBoundary) <:> SetLocal(address) <:>
              GetGlobal(Utils.memoryBoundary) <:> Const(4 * (args.size+1)) <:> Add <:>
              SetGlobal(Utils.memoryBoundary) <:> GetLocal(address) <:> 
              Const(constructor.index) <:> Store <:> 
              argCodes <:> GetLocal(address)
            
            
            case None =>
              cgArgs <:> Call(Utils.fullName(table.getFunction(qname).get.owner, qname))
          }
        
        case Sequence(e1, e2) => cgExpr(e1) <:> Drop <:> cgExpr(e2)

        case Let(df, value, body) =>
          val address = lh.getFreshLocal()
          cgExpr(value) <:> SetLocal(address) <:> 
          cgExpr(body)(locals + (df.name -> address), lh)
        
        case Ite(cond, thenn, elze) =>
          cgExpr(cond) <:> If_i32 <:> cgExpr(thenn) <:> Else <:> cgExpr(elze) <:> End
      
        case Match(scrut, cases) =>

          def matchAndBind(value: Code, pattern: Pattern): (Code, Map[Identifier, Int]) = {
            pattern match {
              case WildcardPattern() => (value <:> Drop <:> Const(1), locals)

              case IdPattern(name) =>
                val idLocal = lh.getFreshLocal()
                (value <:> SetLocal(idLocal) <:> Const(1), locals + (name -> idLocal))
              
              case LiteralPattern(lit) => (value <:> cgExpr(lit) <:> Eq, locals)

              case CaseClassPattern(constr, args) =>
                val constrLocal = lh.getFreshLocal()
                val index = table.getConstructor(constr).get.index

                val argCodeWithBindings = args.zipWithIndex.map{
                  case (arg, idx) => 
                    matchAndBind(GetLocal(constrLocal) <:> Utils.adtField(idx) <:> Load, arg)
                }
                val argCode = argCodeWithBindings.map(_._1)

                val argsCode: Code = {
                  if (args.isEmpty) Const(1)
                  else if (args.lengthCompare(1) == 0) argCode
                  else argCode <:> args.tail.map(arg => And)
                }

                val caseClassCode =
                  value <:> SetLocal(constrLocal) <:> GetLocal(constrLocal) <:> Load <:>
                  Const(index) <:> Eq <:> If_i32 <:>
                  argsCode <:> Else <:> Const(0) <:> End

                val newLocals = locals ++
                  argCodeWithBindings.map(_._2).foldLeft(
                    Map[Identifier, Int]())((bind1, bind2) => bind1 ++ bind2)

                (caseClassCode, newLocals)
            }
          }

          val scrutLocal = lh.getFreshLocal()
          val caseCodes = cases.map(
            caze => (caze, matchAndBind(GetLocal(scrutLocal), caze.pat))).map{
              case (caze,(code, bind)) => code <:> If_i32 <:> cgExpr(caze.expr)(bind, lh) <:> Else
            }

          cgExpr(scrut) <:> SetLocal(scrutLocal) <:> caseCodes <:> 
          mkString("Match error!") <:> Call("Std_printString") <:> 
          Unreachable <:> cases.map(caze => End)

          

        case Error(msg) =>
          cgExpr(StringLiteral("Error: ")) <:> cgExpr(msg) <:> Call(concatImpl.name) <:> 
          Call("Std_printString") <:> Instructions.Unreachable
      }
    }

    Module(
      program.modules.last.name.name,
      defaultImports,
      globalsNo,
      wasmFunctions ++ (program.modules flatMap cgModule)
    )

  }
}
