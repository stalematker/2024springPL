package cs320

import Value._

object Implementation extends Template {

  def interp(expr: Expr, env: Env): Value = expr match {
    
    case Id(x) => env.getOrElse(x, error(s"free identifier: $x"))
    case IntE(n) => IntV(n)
    case BooleanE(b) => BooleanV(b)
    case Add(l, r) => (interp(l, env), interp(r, env)) match {
      case (IntV(lv), IntV(rv)) => IntV(lv + rv)
      case _ => error(s"wrong type")
    }
    case Mul(l, r) => (interp(l, env), interp(r, env)) match {
      case (IntV(lv), IntV(rv)) => IntV(lv * rv)
      case _ => error(s"wrong type")
    }
    case Div(l, r) => (interp(l, env), interp(r, env)) match {
      case (IntV(lv), IntV(rv)) => if (rv != 0) IntV(lv / rv) else error(s"divide by zero")
      case _ => error(s"wrong type")
    }
    case Mod(l, r) => (interp(l, env), interp(r, env)) match {
      case (IntV(lv), IntV(rv)) => if (rv != 0) IntV(lv % rv) else error(s"divide by zero")
      case _ => error(s"wrong type")
    }
    case Eq(l, r) => (interp(l, env), interp(r, env)) match {
      case (IntV(lv), IntV(rv)) => BooleanV(lv == rv)
      case _ => error(s"wrong type")
    }
    case Lt(l, r) => (interp(l, env), interp(r, env)) match {
      case (IntV(lv), IntV(rv)) => BooleanV(lv == rv)
      case _ => error(s"wrong type")
    }
    case If(c, t, f) => interp(c, env) match {
      case BooleanV(true) => interp(t, env)
      case BooleanV(false) => interp(f, env)
      case _ => error(s"wrong type")
    }
    case TupleE(es) => TupleV(es.map(interp(_, env)))
    case Proj(es, i) => interp(es, env) match {
      case TupleV(values) if i > 0 && i <= values.size => values(i - 1)
      case TupleV(_) => error(s"out of bounds")
      case _ => error(s"wrong type")
    }
    case NilE => NilV
    case ConsE(h, t) => (interp(h, env), interp(t, env)) match {
      case (hv, (tv @ (_: ConsV | NilV))) => ConsV(hv, tv)
      case _ => error(s"wrong type")
    }
    case Empty(e) => interp(e, env) match {
        case NilV => BooleanV(true)
        case ConsV(_, _) => BooleanV(false)
        case _ => error(s"wrong type")
    }
    case Head(e) => interp(e, env) match {
      case ConsV(h, _) => h
      case _ => error(s"wrong type")
    }
    case Tail(e) => interp(e, env) match {
      case ConsV(_, t) => t
      case _ => error(s"wrong type")
    }
    case Val(n, e, b) => interp(b, env + (n -> interp(e, env)))
    case Fun(ps, b) => CloV(ps, b, env)
    case RecFuns(functions: List[FunDef], body: Expr) => {
      val recEnv = functions.foldLeft(env) { (currentEnv, funDef) =>
      val closure = CloV(funDef.parameters, funDef.body, currentEnv)
      currentEnv + (funDef.name -> closure)
      }
      functions.foreach {
        funDef => recEnv(funDef.name) match {
          case cloV: CloV => cloV.env = recEnv
          case _ => error(s"wrong type")
        }
      }
      interp(body, recEnv)
    }
    case App(f, arg) => interp(f, env) match {
      case CloV(params, body, fenv) if params.length == arg.length =>
        val argValues = arg.map(interp(_, env))
        interp(body, fenv ++ params.zip(argValues))
      case CloV(_, _, _) => error("wrong number of arguments")
      case _ => error(s"wrong type")
    }
    case Test(e, typ) =>
      val value = interp(e, env)
      BooleanV(value match {
        case IntV(_) => typ == IntT
        case BooleanV(_) => typ == BooleanT
        case TupleV(_) => typ == TupleT
        case NilV | ConsV(_, _) => typ == ListT
        case CloV(_, _, _) => typ == FunctionT
        case _ => false
      })
  }
  def interp(expr: Expr): Value = interp(expr, Map())
}