package cs320

import Value._

sealed trait Handler 

case object NoH extends Handler
case class ExceptionH(e: Expr, env: Env, k: Cont, h: Handler) extends Handler

object Implementation extends Template {

  def interp(expr: Expr, env: Env, hand: Handler, k: Cont): Value = expr match {

    case Id(x) => k(env.getOrElse(x, error(s"free identifier: $x")))
    case IntE(n) => k(IntV(n))
    case BooleanE(value: Boolean) => k(BooleanV(value))
    case Add(l, r) =>
      interp(l, env, hand, lv => 
        interp(r, env, hand, rv => (lv, rv) match {
          case (IntV(lv), IntV(rv)) => k(IntV(lv + rv))
          case _ => error(s"wrong type")
        })
      )
    case Mul(l, r) =>
      interp(l, env, hand, lv => 
        interp(r, env, hand, rv => (lv, rv) match {
          case (IntV(lv), IntV(rv)) => k(IntV(lv * rv))
          case _ => error(s"wrong type")
        })
      )
    case Div(l, r) =>
      interp(l, env, hand, lv => 
        interp(r, env, hand, rv => (lv, rv) match {
          case (IntV(lv), IntV(rv)) => if (rv != 0) k(IntV(lv / rv)) else error(s"divide by zero")
          case _ => error(s"wrong type")
        })
      )
    case Mod(l, r) =>
      interp(l, env, hand, lv => 
        interp(r, env, hand, rv => (lv, rv) match {
          case (IntV(lv), IntV(rv)) => if (rv != 0) k(IntV(lv % rv)) else error(s"divide by zero")
          case _ => error(s"wrong type")
        })
      )
    case Eq(l, r) =>
      interp(l, env, hand, lv => 
        interp(r, env, hand, rv => (lv, rv) match {
          case (IntV(lv), IntV(rv)) => k(BooleanV(lv == rv))
          case _ => error(s"wrong type")
        })
      )
    case Lt(l, r) =>
      interp(l, env, hand, lv => 
        interp(r, env, hand, rv => (lv, rv) match {
          case (IntV(lv), IntV(rv)) => k(BooleanV(lv < rv))
          case _ => error(s"wrong type")
        })
      )
    case If(c, t, f) =>
      interp(c, env, hand, cv =>
        cv match {
          case BooleanV(true) => interp(t, env, hand, k)
          case BooleanV(false) => interp(f, env, hand, k)
          case _ => error(s"wrong type")
        }
      )
    case TupleE(expr) => evaluateList(expr, env, hand, values => k(TupleV(values)))
      
    case Proj(expr, i) =>
      interp(expr, env, hand, ev =>
        ev match {
          case TupleV(values) if i > 0 && i <= values.size => k(values(i-1))
          case TupleV(_) => error(s"out of bounds")
          case _ => error(s"wrong type")
        }
      )
    case NilE => k(NilV)
    case ConsE(h, t) => 
      interp(h, env, hand, hv =>
        interp(t, env, hand, tv => 
          tv match {
            case NilV => k(ConsV(hv,tv))
            case ConsV(_, _) => k(ConsV(hv,tv))
            case _ => error(s"wrong type")
          }
        )
      )
    case Empty(expr) => 
      interp(expr, env, hand, ev =>
        ev match {
          case NilV => k(BooleanV(true))
          case ConsV(_, _) => k(BooleanV(false))
          case _ => error(s"wrong type")
        }
      ) 
    case Head(expr) => 
      interp(expr, env, hand, ev =>
        ev match {
          case ConsV(h, _) => k(h)
          case _ => error(s"wrong type")
        }
      ) 
    case Tail(expr) => 
      interp(expr, env, hand, ev =>
        ev match {
          case ConsV(_, t) => k(t)
          case _ => error(s"wrong type")
        }
      ) 
    case Val(x, expr, b) =>
      interp(expr, env, hand, ev => 
        interp(b, env + (x -> ev), hand, k)
    )
    case Vcc(x, b) => 
      interp(b, env + (x -> ContV(k)), hand, k)
    
    case Fun(p, b) => k(CloV(p, b, env))

    case RecFuns(fun, body) =>
      def makeRecEnv(fun: List[FunDef], cenv: Env): Env = fun match {
        case Nil => cenv
        case FunDef(name, params, fbody) :: tail =>
          val closure = CloV(params, fbody, env)
          makeRecEnv(tail, cenv + (name -> closure))
      }
      def modifyfenv(fun: List[FunDef], cenv: Env): Unit = fun match {
        case Nil => ()
        case FunDef(name, params, fbody) :: t =>
          val cloV = cenv.getOrElse(name, error(s"not found"))
          cloV match {
            case ev@CloV(parameters: List[String], body: Expr, fenv: Env) =>
              val nenv = fenv ++ cenv
              ev.env = nenv
            case _ => error(s"wrong type")
          }
          modifyfenv(t,cenv)
      }
      val cenv = makeRecEnv(fun, Map())
      modifyfenv(fun, cenv)
      interp(body, env++cenv, hand, k)

    case App(fun, args) =>
      interp(fun, env, hand, fv => {
        evaluateList(args, env, hand, av => {
          fv match {
            case CloV(params, body, fenv) if params.length == av.length =>
              interp(body, fenv ++ params.zip(av), hand, k)
            case ContV(cont) if args.length == 1 => cont(av.head)
            case _ => error(s"wrong type")
          }
        })
      })
    case Test(expr, typ) =>
      interp(expr, env, hand, T => 
        T match {
          case IntV(_) => k(BooleanV(typ == IntT))
          case BooleanV(_) => k(BooleanV(typ == BooleanT))
          case TupleV(_) => k(BooleanV(typ == TupleT))
          case NilV => k(BooleanV(typ == ListT))
          case ConsV(_, _) => k(BooleanV(typ == ListT))
          case CloV(_, _, _) => k(BooleanV(typ == FunctionT))
          case ContV(_) => k(BooleanV(typ == FunctionT))
          case _ => k(BooleanV(false))
        }
      )
    case Throw(expr) =>
      interp(expr, env, hand, ev => 
        hand match {
          case ExceptionH(eh, envh, kh, hh) =>
            interp(eh, envh, hh, vh => vh match {
              case CloV(List(x), b, env) => interp(b, env + (x -> ev), hh, kh)
              case ContV(kh) => kh(ev)
              case _ => error(s"wrong type")
            })
          case NoH => error(s"wrong handle")
        }
      )
    case Try(expression, handler) =>
      interp(expression, env, ExceptionH(handler, env, k, hand), k)
  }  

  def interp(expr: Expr): Value = interp(expr,Map(), NoH, x => x)

  private def evaluateList(exprs: List[Expr], env: Env, hand: Handler, result: List[Value] => Value): Value = {
    exprs match {
      case Nil => result(Nil)
      case h :: t =>
        interp(h, env, hand, hv =>
          evaluateList(t, env, hand, tv => result(hv :: tv))
        )
    }
  }
}
