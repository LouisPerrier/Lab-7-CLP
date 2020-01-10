package amyc
package analyzer

import utils._
import ast.{Identifier, NominalTreeModule => N, SymbolicTreeModule => S}

import scala.collection.mutable.HashMap

// Name analyzer for Amy
// Takes a nominal program (names are plain strings, qualified names are string pairs)
// and returns a symbolic program, where all names have been resolved to unique Identifiers.
// Rejects programs that violate the Amy naming rules.
// Also populates and returns the symbol table.
object NameAnalyzer extends Pipeline[N.Program, (S.Program, SymbolTable)] {
  def run(ctx: Context)(p: N.Program): (S.Program, SymbolTable) = {
    import ctx.reporter._

    // Step 0: Initialize symbol table
    val table = new SymbolTable

    var classFunDefs = HashMap[(String, String), N.ClassOrFunDef]()

    // Step 1: Add modules to table 
    val modNames = p.modules.groupBy(_.name)
    modNames.foreach { case (name, modules) =>
      if (modules.size > 1) {
        fatal(s"Two modules named $name in program", modules.head.position)
      }
    }

    modNames.keys.toList foreach table.addModule


    // Helper method: will transform a nominal type 'tt' to a symbolic type,
    // given that we are within module 'inModule'.
    def transformType(tt: N.TypeTree, inModule: String): S.Type = {
      tt.tpe match {
        case N.IntType => S.IntType
        case N.BooleanType => S.BooleanType
        case N.StringType => S.StringType
        case N.UnitType => S.UnitType
        case N.ClassType(qn@N.QualifiedName(module, name)) =>
          table.getType(module getOrElse inModule, name) match {
            case Some(symbol) =>
              S.ClassType(symbol)
            case None =>
              fatal(s"Could not find type $qn", tt)
          }
      }
    }

    // Step 2: Check name uniqueness of definitions in each module
    // TODO
    p.modules.foreach { case module => 
      module.defs.groupBy(_.name).foreach { case (name, defs) =>
        if (defs.size > 1) {
          fatal(s"Two definitions named $name in module ${module.name}", defs.head.position)
        }
      }
    }
    

    // Step 3: Discover types and add them to symbol table
    p.modules.foreach { case module =>
      val owner = module.name
      module.defs.foreach {
        case N.AbstractClassDef(name) => table.addType(owner, name)
        case _ =>
      }
    }

    // Step 4: Discover type constructors, add them to table
    p.modules.foreach { case module =>
      val owner = module.name
      module.defs.foreach {
        case cc@N.CaseClassDef(name, fields, parent) =>
          val argTypes = fields.map(p => transformType(p.tt, owner))
          classFunDefs += (owner, name) -> cc
          table.addConstructor(owner, name, argTypes, table.getType(owner, parent).getOrElse(
            fatal(s"Unknow type $owner", cc)
          ))
        case _ =>
      }
    }

    // Step 5: Discover functions signatures, add them to table
    // TODO
    p.modules.foreach { case module =>
      val owner = module.name
      module.defs.foreach {
        case fd@N.FunDef(name, params, retType, _) =>
          val argTypes = params.map(param => param.tt).map(tt => transformType(tt, owner))
          classFunDefs += (owner, name) -> fd
          table.addFunction(owner, name, argTypes, transformType(retType, owner))
        case _ =>
      }
    }
    

    // Step 6: We now know all definitions in the program.
    //         Reconstruct modules and analyse function bodies/ expressions
    
    // This part is split into three transfrom functions,
    // for definitions, FunDefs, and expressions.
    // Keep in mind that we transform constructs of the NominalTreeModule 'N' to respective constructs of the SymbolicTreeModule 'S'.
    // transformFunDef is given as an example, as well as some code for the other ones

    def transformDef(df: N.ClassOrFunDef, module: String): S.ClassOrFunDef = { df match {
      case N.AbstractClassDef(name) =>
        // TODO
        S.AbstractClassDef(table.getType(module, name).get)
      case N.CaseClassDef(name, _, _) =>
        // TODO
        val constructor = table.getConstructor(module, name).get
        val fields = constructor._2.argTypes.map(t => S.TypeTree(t))
        S.CaseClassDef(constructor._1, fields ,constructor._2.parent)
      case fd: N.FunDef =>
        transformFunDef(fd, module)
    }}.setPos(df)

    def transformFunDef(fd: N.FunDef, module: String): S.FunDef = {
      val N.FunDef(name, params, retType, body) = fd
      val Some((sym, sig)) = table.getFunction(module, name)

      params.groupBy(_.name).foreach { case (name, ps) =>
        if (ps.size > 1) {
          fatal(s"Two parameters named $name in function ${fd.name}", fd)
        }
      }

      val paramNames = params.map(_.name)

      val newParams = params zip sig.argTypes map { case (pd@N.ParamDef(name, tt, _), tpe) =>
        val s = Identifier.fresh(name)
        S.ParamDef(s, S.TypeTree(tpe).setPos(tt)).setPos(pd)
      }

      val paramsMap = paramNames.zip(newParams.map(_.name)).toMap

      S.FunDef(
        sym,
        newParams,
        S.TypeTree(sig.retType).setPos(retType),
        transformExpr(body)(module, (paramsMap, Map()))
      ).setPos(fd)
    }

    // This function takes as implicit a pair of two maps:
    // The first is a map from names of parameters to their unique identifiers,
    // the second is similar for local variables.
    // Make sure to update them correctly if needed given the scoping rules of Amy
    def transformExpr(expr: N.Expr)
                     (implicit module: String, names: (Map[String, Identifier], Map[String, Identifier])): S.Expr = {
      val (params, locals) = names
      val res = expr match {
        case N.Match(scrut, cases) =>
          // Returns a transformed pattern along with all bindings
          // from strings to unique identifiers for names bound in the pattern.
          // Also, calls 'fatal' if a new name violates the Amy naming rules.
          def transformPattern(pat: N.Pattern): (S.Pattern, List[(String, Identifier)]) = {
            // TODO
            pat match {
              case N.WildcardPattern() => (S.WildcardPattern().setPos(pat), Nil)
              case N.IdPattern(name) =>
                val uniqueName = Identifier.fresh(name)
                if (locals.contains(name))
                  fatal(s"Duplicate definition of $name", pat)
                (S.IdPattern(uniqueName).setPos(pat), List((name, uniqueName)))
              case N.LiteralPattern(lit) =>
                val newLit = (lit match {
                  case N.IntLiteral(value) => S.IntLiteral(value)
                  case N.BooleanLiteral(value) => S.BooleanLiteral(value)
                  case N.StringLiteral(value) => S.StringLiteral(value)
                  case N.UnitLiteral() => S.UnitLiteral()
                }).setPos(lit)
                (S.LiteralPattern(newLit).setPos(pat), Nil)
              case N.CaseClassPattern(constr, args) =>
                val owner = constr.module.getOrElse(module)
                val newConstr = table.getConstructor(owner, constr.name).getOrElse(
                  fatal(s"Unknown class ${constr.name} in module $owner", pat)
                )
                if (newConstr._2.argTypes.size != args.size)
                  fatal(s"Unexpected number of arguments for class $owner.${constr.name}", pat)
                
                val newArgs = args.map(arg => transformPattern(arg))
                val defs = newArgs.flatMap(arg => arg._2)
                defs.groupBy(_._1).foreach{
                  case (name,l) => if (l.size != 1)
                             fatal(s"Duplicate definition of $name", pat)
                }
                (S.CaseClassPattern(newConstr._1, newArgs.unzip._1).setPos(pat), defs)
            }
          }

          def transformCase(cse: N.MatchCase) = {
            val N.MatchCase(pat, rhs) = cse
            val (newPat, moreLocals) = transformPattern(pat)
            moreLocals.foreach{case (name, _) =>
              if (locals.keySet.contains(name))
                fatal(s"Duplicate definition of $name", pat)
            }
            S.MatchCase(newPat, transformExpr(rhs)(module, (params, locals ++ moreLocals.toMap))).setPos(cse)
          }

          S.Match(transformExpr(scrut), cases.map(transformCase))

        case N.Variable(name) =>
          val newName = locals.getOrElse(name, 
            params.getOrElse(name, fatal(s"Unknown identifier $name", expr)))
          S.Variable(newName)
        
        case N.IntLiteral(value) => S.IntLiteral(value)
        case N.BooleanLiteral(value) => S.BooleanLiteral(value)
        case N.StringLiteral(value) => S.StringLiteral(value)
        case N.UnitLiteral() => S.UnitLiteral()

        case N.Plus(lhs, rhs) => S.Plus(transformExpr(lhs), transformExpr(rhs))
        case N.Minus(lhs, rhs) => S.Minus(transformExpr(lhs), transformExpr(rhs))
        case N.Times(lhs, rhs) => S.Times(transformExpr(lhs), transformExpr(rhs))
        case N.Mod(lhs, rhs) => S.Mod(transformExpr(lhs), transformExpr(rhs))
        case N.Div(lhs, rhs) => S.Div(transformExpr(lhs), transformExpr(rhs))
        case N.And(lhs, rhs) => S.And(transformExpr(lhs), transformExpr(rhs))
        case N.Or(lhs, rhs) => S.Or(transformExpr(lhs), transformExpr(rhs))
        case N.LessThan(lhs, rhs) => S.LessThan(transformExpr(lhs), transformExpr(rhs))
        case N.LessEquals(lhs, rhs) => S.LessEquals(transformExpr(lhs), transformExpr(rhs))
        case N.Equals(lhs, rhs) => S.Equals(transformExpr(lhs), transformExpr(rhs))
        case N.Concat(lhs, rhs) => S.Concat(transformExpr(lhs), transformExpr(rhs))

        case N.Not(e) => S.Not(transformExpr(e))
        case N.Neg(e) => S.Neg(transformExpr(e))

        case N.Error(msg) => S.Error(transformExpr(msg))

        case N.Call(qname, args) =>
          val owner = qname.module.getOrElse(module)
          val constr = table.getConstructor(owner, qname.name).getOrElse(
            table.getFunction(owner, qname.name).getOrElse(
              fatal(s"No definition for ${qname.name} in module $owner", expr)
            )
          )
          
          /*if (constr._2.argTypes.size != args.size)
            fatal(s"Unexpected number of arguments for function $owner.${qname.name}", expr)*/
          
          val fd = classFunDefs((owner, qname.name))

          fd match {
            case N.FunDef(_, p, _, _) => {
              val indexToNames = (0 until p.size).zip(p.map(_.name)).toMap
              var namesToValues = HashMap[N.Name, Option[N.Expr]]() ++ p.map(_.name).zip(p.map(_.value)).toMap
              args.zipWithIndex.foreach{
                case ((None, exp),idx) => namesToValues(indexToNames(idx)) = Some(exp)
                case ((Some(id), exp),idx) => namesToValues(id) = Some(exp)
              }
              if (namesToValues.values.toSet.contains(None))
                fatal(s"Named argument has no correponding parameter in function definition", expr)
              else
                {
                val values = indexToNames.keys.toList.sorted.map(indexToNames(_)).map(namesToValues(_))
                S.Call(constr._1, values.map(v => transformExpr(v.get)))
                }
            }

            case N.CaseClassDef(_, f, _) => {
              val indexToNames = (0 until f.size).zip(f.map(_.name)).toMap
              var namesToValues = HashMap[N.Name, Option[N.Expr]]() ++ f.map(_.name).zip(f.map(_.value)).toMap
              args.zipWithIndex.foreach{
                case ((None, exp),idx) => namesToValues(indexToNames(idx)) = Some(exp)
                case ((Some(id), exp),idx) => namesToValues(id) = Some(exp)
              }
              if (namesToValues.values.toSet.contains(None))
                fatal(s"Named argument has no correponding field in case class definition", expr)
              else 
                {
                val values = indexToNames.keys.toList.sorted.map(indexToNames(_)).map(namesToValues(_))
                S.Call(constr._1, values.map(v => transformExpr(v.get)))
                }
            }
          }

        case N.Sequence(e1, e2) => S.Sequence(transformExpr(e1), transformExpr(e2))

        case N.Let(df, value, body) =>
          if (locals.contains(df.name))
            fatal(s"Duplicate definition of ${df.name}", expr)
          val name = Identifier.fresh(df.name)
          val tt = S.TypeTree(transformType(df.tt, module))
          val newBody = transformExpr(body)(module, (params, locals + (df.name -> name)))
          S.Let(S.ParamDef(name, tt), transformExpr(value), newBody)
      
        case N.Ite(cond, thenn, elze) =>
          S.Ite(transformExpr(cond), transformExpr(thenn), transformExpr(elze))
      }
      res.setPos(expr)
    }

    // Putting it all together to construct the final program for step 6.
    val newProgram = S.Program(
      p.modules map { case mod@N.ModuleDef(name, defs, optExpr) =>
        S.ModuleDef(
          table.getModule(name).get,
          defs map (transformDef(_, name)),
          optExpr map (transformExpr(_)(name, (Map(), Map())))
        ).setPos(mod)
      }
    ).setPos(p)

    (newProgram, table)

  }
}
