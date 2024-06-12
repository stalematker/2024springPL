package cs320

object Implementation extends Template {

  def typeCheck(e: Typed.Expr): Typed.Type = T.typeCheck(e)
  def interp(e: Untyped.Expr): Untyped.Value = U.interp(e)

  object T {
    import Typed._

    case class TypeScheme(t: Type, typeVars: List[VarT])
    case class TypeEnv(
      vars: Map[String, (TypeScheme, Boolean)] = Map(),
      typeDefs: Map[String, TypeDef] = Map()
    ) {
      def addTypeDef(name: String, tdef: TypeDef): TypeEnv = copy(typeDefs = typeDefs + (name -> tdef))
      def addVar(name: String, t: TypeScheme, mut: Boolean): TypeEnv = copy(vars = vars + (name -> (t, mut)))
    }

    def mustSame(l: Type, r: Type): Type = if (same(l, r)) l else error("types are not the same")
    def same(l: Type, r: Type): Boolean = (l, r) match {
      case (ArrowT(p1s, r1), ArrowT(p2s, r2)) => listSame(p1s zip p2s) && same(r1, r2)
      case (AppT(n1, targs1), AppT(n2, targs2)) => n1 == n2 && listSame(targs1 zip targs2)
      case (IntT, IntT) | (BooleanT, BooleanT) | (UnitT, UnitT) => true
      case (VarT(t1), VarT(t2)) => t1 == t2
      case _ => false
    }

    def listSame(pairs: List[(Type, Type)]): Boolean = pairs.forall { case (l, r) => same(l, r) }

    def typeSubstitute(t: Type, typeVars: List[VarT], targs: List[Type]): Type = t match {
      case ArrowT(types, rtype) => ArrowT(types.map(typeSubstitute(_, typeVars, targs)), typeSubstitute(rtype, typeVars, targs))
      case AppT(name, tvars) => AppT(name, tvars.map(typeSubstitute(_, typeVars, targs)))
      case v@VarT(_) => typeVars.indexOf(v) match {
        case -1 => v
        case index => targs(index)
      }
      case _ => t
    }

    def typeCheck(expr: Expr, tyEnv: TypeEnv): Type = expr match {
      case Id(name, targs) =>
        listValidCheck(targs, tyEnv)
        val (typeScheme, _) = tyEnv.vars.getOrElse(name, error("variable not in environment"))
        if (targs.length != typeScheme.typeVars.length) error("length mismatch")
        if (targs.isEmpty) typeScheme.t else typeSubstitute(typeScheme.t, typeScheme.typeVars, targs)
      case IntE(_) => IntT
      case BooleanE(_) => BooleanT
      case UnitE => UnitT
      case Add(left, right) => checkBinaryOp(left, right, tyEnv, IntT)
      case Mul(left, right) => checkBinaryOp(left, right, tyEnv, IntT)
      case Div(left, right) => checkBinaryOp(left, right, tyEnv, IntT)
      case Mod(left, right) => checkBinaryOp(left, right, tyEnv, IntT)
      case Eq(left, right) => checkBinaryOp(left, right, tyEnv, BooleanT)
      case Lt(left, right) => checkBinaryOp(left, right, tyEnv, BooleanT)
      case Sequence(left, right) => 
        validType(typeCheck(left, tyEnv), tyEnv)
        typeCheck(right, tyEnv)
      case If(cond, texpr, fexpr) =>
        mustSame(typeCheck(cond, tyEnv), BooleanT)
        mustSame(typeCheck(texpr, tyEnv), typeCheck(fexpr, tyEnv))
      case Val(mut, name, typ, e, b) => 
        val t1 = typ.map(validType(_, tyEnv)).getOrElse(typeCheck(e, tyEnv))
        mustSame(t1, typeCheck(e, tyEnv))
        typeCheck(b, tyEnv.addVar(name, TypeScheme(t1, List()), mut))
      case RecBinds(defs, body) => 
        val newtyEnv = defs.foldLeft(tyEnv) {
          case (env, Lazy(name, typ, expr)) =>
            validType(typ, env)
            val newEnv = env.addVar(name, TypeScheme(typ, List()), false)
            mustSame(typ, typeCheck(expr, newEnv))
            newEnv
          case (env, RecFun(name, tparams, params, rtype, body)) =>
            val tvars = tparams.map(VarT)
            env.addVar(name, TypeScheme(ArrowT(params.map(_._2), rtype), tvars), false)
          case (env, td@TypeDef(name, tparams, variants)) =>
            if (env.typeDefs.contains(name)) error("type definition already exists")
            val newEnv = env.addTypeDef(name, td)
            val tvars = tparams.map(VarT)
            variants.foldLeft(newEnv) {
              case (e, Variant(name, Nil)) => e.addVar(name, TypeScheme(AppT(name, tvars), tvars), false)
              case (e, Variant(name, params)) => e.addVar(name, TypeScheme(ArrowT(params, AppT(name, tvars)), tvars), false)
            }
        }
        defs.foreach {
          case RecFun(name, tparams, params, rtype, body) =>
            val paramAddedTyEnv = (tparams zip tparams.map(VarT)).foldLeft(newtyEnv) {
              case (env, (name, tvar)) => env.addVar(name, TypeScheme(tvar, List()), false)
            }
            val ntyEnv = params.foldLeft(paramAddedTyEnv) {
              case (env, (name, typ)) => env.addVar(name, TypeScheme(typ, List()), false)
            }
            mustSame(rtype, typeCheck(body, ntyEnv))
          case TypeDef(_, _, variants) =>
            variants.foreach(v => listValidCheck(v.params, newtyEnv))
          case _ => ()
        }
        val result = typeCheck(body, newtyEnv)
        validType(result, tyEnv)
        result
      case Fun(params, body) =>
        val (names, types) = params.unzip
        listValidCheck(types, tyEnv)
        val returnT = typeCheck(body, params.foldLeft(tyEnv) {
          case (env, (name, typ)) => env.addVar(name, TypeScheme(typ, List()), false)
        })
        ArrowT(types, returnT)
      case Assign(name, expr) =>
        val (typeScheme, mut) = tyEnv.vars.getOrElse(name, error("variable not in environment"))
        if (typeScheme.typeVars.nonEmpty) error("length mismatch")
        if (!mut) error("variable is not mutable")
        mustSame(typeScheme.t, typeCheck(expr, tyEnv))
        UnitT
      case App(fun, args) =>
        typeCheck(fun, tyEnv) match {
          case ArrowT(ptypes, rtype) =>
            if (args.length != ptypes.length) error("length mismatch")
            args.zip(ptypes).foreach { case (arg, ptype) => mustSame(ptype, typeCheck(arg, tyEnv)) }
            rtype
          case _ => error("type mismatch")
        }
      case Match(expr, cases) =>
        typeCheck(expr, tyEnv) match {
          case AppT(name, targs) =>
            val typeDef = tyEnv.typeDefs.getOrElse(name, error("type definition not found"))
            if (typeDef.tparams.length != targs.length || typeDef.variants.length != cases.length) error("length mismatch")
            val tlist = cases.map(typeCheckCase(_, typeDef.variants, typeDef.tparams, targs, tyEnv))
            tlist.reduce(mustSame)
          case _ => error("type mismatch")
        }
    }

    def checkBinaryOp(left: Expr, right: Expr, tyEnv: TypeEnv, expected: Type): Type = {
      (typeCheck(left, tyEnv), typeCheck(right, tyEnv)) match {
        case (`expected`, `expected`) => expected
        case _ => error("type mismatch")
      }
    }

    def typeCheckCase(c: Case, variants: List[Variant], tparams: List[String], targs: List[Type], tyEnv: TypeEnv): Type = {
      if (tparams.length != targs.length) error("length mismatch")
      val variant = variants.find(_.name == c.variant).getOrElse(error("variant not found"))
      if (variant.params.length != c.names.length) error("length mismatch")
      val tvars = tparams.map(VarT)
      val newTyEnv = (c.names zip variant.params).foldLeft(tyEnv) {
        case (env, (name, typ)) => env.addVar(name, TypeScheme(typeSubstitute(typ, tvars, targs), List()), false)
      }
      typeCheck(c.body, newTyEnv)
    }

    def validType(ty: Type, tyEnv: TypeEnv): Type = ty match {
      case AppT(name, targs) =>
        listValidCheck(targs, tyEnv)
        val tydef = tyEnv.typeDefs.getOrElse(name, error("type not in environment"))
        if (targs.length != tydef.tparams.length) error("length mismatch")
        ty
      case VarT(name) =>
        if (tyEnv.vars.contains(name)) ty else error("type not in environment")
      case IntT | BooleanT | UnitT => ty
      case ArrowT(ptypes, rtype) =>
        listValidCheck(ptypes, tyEnv)
        validType(rtype, tyEnv)
        ty
    }

    def listValidCheck(tyList: List[Type], tyEnv: TypeEnv): Unit = tyList.foreach(validType(_, tyEnv))
    def typeCheck(expr: Expr): Type = typeCheck(expr, TypeEnv())
  }

  object U {
    import Untyped._

    type Sto = Map[Addr, Value]

    def interp(expr: Expr, env: Env, sto: Sto): (Value, Sto) = expr match {
      case Id(name) => 
        val a = env.getOrElse(name, error("variable not in environment"))
        val v = sto.getOrElse(a, error("variable not in store"))
        v match {
          case ExprV(e, env) => interp(e, env, sto).mapBoth(v1 => v1 -> (a -> v1))
          case _ => v -> sto
        }
      case IntE(value) => IntV(value) -> sto
      case BooleanE(value) => BooleanV(value) -> sto
      case UnitE => UnitV -> sto
      case Add(left, right) => binaryOp(left, right, env, sto, IntVadd)
      case Mul(left, right) => binaryOp(left, right, env, sto, IntVmul)
      case Div(left, right) => binaryOp(left, right, env, sto, IntVdiv)
      case Mod(left, right) => binaryOp(left, right, env, sto, IntVmod)
      case Eq(left, right) => binaryOp(left, right, env, sto, IntVeq)
      case Lt(left, right) => binaryOp(left, right, env, sto, IntVlt)
      case Sequence(left, right) =>
        val (lv, ls) = interp(left, env, sto)
        interp(right, env, ls)
      case If(cond, texpr, fexpr) =>
        interp(cond, env, sto) match {
          case (BooleanV(true), s1) => interp(texpr, env, s1)
          case (BooleanV(false), s1) => interp(fexpr, env, s1)
          case _ => error("type mismatch")
        }
      case Val(name, expr, body) =>
        val (v1, s1) = interp(expr, env, sto)
        val a = malloc(s1)
        interp(body, env + (name -> a), s1 + (a -> v1))
      case RecBinds(defs, body) => 
        val (nenv, nsto) = defs.foldLeft(env -> sto) {
          case ((e, s), Lazy(name, expr)) =>
            val addr = malloc(s)
            e + (name -> addr) -> (s + (addr -> UnitV))
          case ((e, s), RecFun(name, params, body)) =>
            val addr = malloc(s)
            e + (name -> addr) -> (s + (addr -> UnitV))
          case ((e, s), TypeDef(variants)) =>
            val (ne, ns) = variants.foldLeft(e -> s) {
              case ((env, sto), Variant(name, Nil)) =>
                val addr = malloc(sto)
                env + (name -> addr) -> (sto + (addr -> UnitV))
              case ((env, sto), Variant(name, _)) =>
                val addr = malloc(sto)
                env + (name -> addr) -> (sto + (addr -> UnitV))
            }
            ne -> ns
        }
        val finalSto = defs.foldLeft(nsto) {
          case (s, Lazy(name, expr)) =>
            val addr = nenv.getOrElse(name, error("variable not in environment"))
            s + (addr -> ExprV(expr, nenv))
          case (s, RecFun(name, params, body)) =>
            val addr = nenv.getOrElse(name, error("variable not in environment"))
            s + (addr -> CloV(params, body, nenv))
          case (s, TypeDef(variants)) =>
            variants.foldLeft(s) {
              case (sto, Variant(name, Nil)) =>
                val addr = nenv.getOrElse(name, error("variable not in environment"))
                sto + (addr -> VariantV(name, List()))
              case (sto, Variant(name, _)) =>
                val addr = nenv.getOrElse(name, error("variable not in environment"))
                sto + (addr -> ConstructorV(name))
            }
        }
        interp(body, nenv, finalSto)
      case Fun(params, body) => CloV(params, body, env) -> sto
      case Assign(name, expr) => 
        val addr = env.getOrElse(name, error("variable not in environment"))
        val (v1, s1) = interp(expr, env, sto)
        UnitV -> (s1 + (addr -> v1))
      case App(fun, args) =>
        val (v, s) = interp(fun, env, sto)
        val (vl, ns) = args.foldLeft(List.empty[Value] -> s) {
          case ((values, sto), arg) => 
            val (v, s) = interp(arg, env, sto)
            (values :+ v) -> s
        }
        v match {
          case CloV(params, body, fenv) =>
            if (args.length != params.length) error("length mismatch")
            val (e, s) = (params zip vl).foldLeft(fenv -> ns) {
              case ((env, sto), (str, v)) =>
                val addr = malloc(sto)
                (env + (str -> addr)) -> (sto + (addr -> v))
            }
            interp(body, e, s)
          case ConstructorV(name) => VariantV(name, vl) -> ns
          case _ => error("type mismatch")
        }
      case Match(expr, cases) =>
        interp(expr, env, sto) match {
          case (VariantV(name, values), s) =>
            val caseMatch = cases.find(_.variant == name).getOrElse(error("variant not found"))
            if (values.length != caseMatch.names.length) error("length mismatch")
            val (e, s) = (caseMatch.names zip values).foldLeft(env -> s) {
              case ((env, sto), (str, v)) =>
                val addr = malloc(sto)
                (env + (str -> addr)) -> (sto + (addr -> v))
            }
            interp(caseMatch.body, e, s)
          case _ => error("type mismatch")
        }
    }

    def binaryOp(left: Expr, right: Expr, env: Env, sto: Sto, op: (Value, Value) => Value): (Value, Sto) = {
      val (lv, ls) = interp(left, env, sto)
      val (rv, rs) = interp(right, env, ls)
      op(lv, rv) -> rs
    }

    def IntVadd(left: Value, right: Value): Value = (left, right) match {
      case (IntV(x), IntV(y)) => IntV(x + y)
      case _ => error("type mismatch")
    }
    def IntVmul(left: Value, right: Value): Value = (left, right) match {
      case (IntV(x), IntV(y)) => IntV(x * y)
      case _ => error("type mismatch")
    }
    def IntVdiv(left: Value, right: Value): Value = (left, right) match {
      case (IntV(x), IntV(y)) => if (y == 0) error("divide by zero") else IntV(x / y)
      case _ => error("type mismatch")
    }
    def IntVmod(left: Value, right: Value): Value = (left, right) match {
      case (IntV(x), IntV(y)) => if (y == 0) error("divide by zero") else IntV(x % y)
      case _ => error("type mismatch")
    }
    def IntVeq(left: Value, right: Value): Value = (left, right) match {
      case (IntV(x), IntV(y)) => BooleanV(x == y)
      case _ => error("type mismatch")
    }
    def IntVlt(left: Value, right: Value): Value = (left, right) match {
      case (IntV(x), IntV(y)) => BooleanV(x < y)
      case _ => error("type mismatch")
    }

    def interp(expr: Expr): Value = interp(expr, Map(), Map())._1
    private def malloc(sto: Sto): Addr = sto.keys.maxOption.map(_ + 1).getOrElse(0)
  }
}
