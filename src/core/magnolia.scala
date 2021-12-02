package magnolia1

import scala.deriving.Mirror
import scala.compiletime.*
import scala.quoted.*
import scala.reflect.*
import Macro.*

trait AutoDerivation[TypeClass[_]] extends Derivation[TypeClass]:
  inline given autoDerived[A]: TypeClass[A] = derived

trait Derivation[TypeClass[_]]:
  type Typeclass[T] = TypeClass[T]
  def split[T](ctx: SealedTrait[Typeclass, T]): Typeclass[T]
  def join[T](ctx: CaseClass[Typeclass, T]): Typeclass[T]

  inline def derived[T]: Typeclass[T] = doDerive[T]

  inline def doDerive[T]: Typeclass[T] = 
    inline if isProduct[T] then
      val cc = new CaseClass[Typeclass, T](
        typeInfo[T],
        isObject[T],
        isValueClass[T],
        Derivation.getParams[Typeclass, T](this),
        anns[T],
        typeAnns[T]
      ) {
        def construct[PType](makeParam: Param => PType)(using ClassTag[PType]): T = ???
        def rawConstruct(fieldValues: Seq[Any]): T = ???
        def constructEither[Err, PType: ClassTag](makeParam: Param => Either[Err, PType]): Either[List[Err], T] = ???
        def constructMonadic[M[_]: Monadic, PType: ClassTag](makeParam: Param => M[PType]): M[T] = ???
      }
      join(cc)
    else
      val sealedTrait = SealedTrait[Typeclass, T](
        typeInfo[T],
        Derivation.getSubtypes[Typeclass, T](this),
        List[Any](),
        paramTypeAnns[T],
        false
      )
      split(sealedTrait)

end Derivation

object Derivation:

  inline def getParams[Typeclass[_], T](fallback: Derivation[Typeclass]): List[CaseClass.Param[Typeclass, T]] =
    ${ getParamsImpl[Typeclass, T]('fallback) }
  def getParamsImpl[Typeclass[_]: Type, T: Type](using Quotes)(fallback: Expr[Derivation[Typeclass]]): Expr[List[CaseClass.Param[Typeclass, T]]] =
    new DerivationImpl(using quotes).getParamsImpl[Typeclass, T](fallback)

  inline def getSubtypes[Typeclass[_], T](fallback: Derivation[Typeclass]): List[SealedTrait.Subtype[Typeclass, T, _]] =
    ${ getSubtypesImpl[Typeclass, T]('fallback) }
  def getSubtypesImpl[Typeclass[_]: Type, T: Type](fallback: Expr[Derivation[Typeclass]])(using Quotes): Expr[List[SealedTrait.Subtype[Typeclass, T, _]]] =
    new DerivationImpl(using quotes).getSubtypesImpl[Typeclass, T](fallback)

end Derivation

class DerivationImpl(using Quotes):
  import quotes.reflect.*

  private def isRepeated[T](tpeRepr: TypeRepr): Boolean = tpeRepr match
    case a: AnnotatedType =>
      a.annotation.tpe match
        case tr: TypeRef => tr.name == "Repeated"
        case _           => false
    case _ => false

  private def isObject(typeRepr: TypeRepr): Boolean =
    import quotes.reflect.*

    typeRepr.typeSymbol.flags.is(Flags.Module)

  private def typeInfo(tpe: TypeRepr): Expr[TypeInfo] =
    import quotes.reflect._

    def normalizedName(s: Symbol): String = if s.flags.is(Flags.Module) then s.name.stripSuffix("$") else s.name
    def name(tpe: TypeRepr): Expr[String] = tpe match
      case TermRef(typeRepr, name) if tpe.typeSymbol.flags.is(Flags.Module) => Expr(name.stripSuffix("$"))
      case TermRef(typeRepr, name) => Expr(name)
      case _ => Expr(normalizedName(tpe.typeSymbol))

    def ownerNameChain(sym: Symbol): List[String] =
      if sym.isNoSymbol then List.empty
      else if sym == defn.EmptyPackageClass then List.empty
      else if sym == defn.RootPackage then List.empty
      else if sym == defn.RootClass then List.empty
      else ownerNameChain(sym.owner) :+ normalizedName(sym)

    def owner(tpe: TypeRepr): Expr[String] = Expr(
      ownerNameChain(tpe.typeSymbol.maybeOwner).mkString(".")
    )

    tpe match
      case AppliedType(tpe, args) =>
        '{
          TypeInfo(
            ${ owner(tpe) },
            ${ name(tpe) },
            ${ Expr.ofList(args.map(typeInfo)) }
          )
        }
      case _ =>
        '{ TypeInfo(${ owner(tpe) }, ${ name(tpe) }, Nil) }

  def to[T: Type, R: Type](f: Expr[T] => Expr[R])(using Quotes): Expr[T => R] = '{ (x: T) => ${ f('x) } }

  private def isType[T: Type](typeRepr: TypeRepr): Expr[T => Boolean] = to { other =>
    Expr(other.asTerm.tpe == typeRepr)
  }

  private def asType[T: Type, S: Type](parent: TypeTree, child: TypeTree): Expr[T => S & T] = to[T, S & T] { t =>
    val resultTypeRepr = AndType(child.tpe, parent.tpe)
    val resultTypeTree = TypeTree.of(using resultTypeRepr.asType)
    println(resultTypeTree)
    TypeApply(Select.unique(t.asTerm, "asInstanceOf"), List(resultTypeTree)).asExprOf[S & T]
  }

  private def getTypeAnnotations(t: TypeRepr): List[Term] = t match
    case AnnotatedType(inner, ann) => ann :: getTypeAnnotations(inner)
    case _                         => Nil

  private def filterAnnotations(annotations: List[Term]): List[Term] =
    annotations.filter { a =>
      a.tpe.typeSymbol.maybeOwner.isNoSymbol ||
        a.tpe.typeSymbol.owner.fullName != "scala.annotation.internal"
    }

  private def termFromInlinedTypeApplyUnsafe(t: Term): Term = t match
    case Inlined(_, _, TypeApply(term, _)) => term

  private def wrapInCallByNeedTerm(term: Term, tpt: TypeTree): Term =
    val callByNeedTerm = '{CallByNeed}.asTerm
    val callByNeedApply = TypeRepr.of[CallByNeed.type].termSymbol.declaredMethod("apply").head
    Apply(TypeApply(Select(callByNeedTerm, callByNeedApply), List(tpt)), List(term))

  def getParamsImpl[Typeclass[_]: Type, T: Type](fallback: Expr[Derivation[Typeclass]]): Expr[List[CaseClass.Param[Typeclass, T]]] =

    val typeSymbol = TypeRepr.of[T].typeSymbol

    val paramObj = '{CaseClass.Param}.asTerm
    val paramConstrSymbol = TypeRepr.of[CaseClass.Param.type].termSymbol.declaredMethod("apply").head

    val annotations = paramAnns[T].to(Map)
    val typeAnnotations = paramTypeAnns[T].to(Map)

    Expr.ofList {
      typeSymbol.caseFields.zipWithIndex.collect {
        case (paramSymbol: Symbol, idx: Int) =>
          val valdef: ValDef = paramSymbol.tree.asInstanceOf[ValDef]
          val paramTypeTree = valdef.tpt
          val paramTypeclassTree = Applied(TypeTree.of[Typeclass], List(paramTypeTree))
          val summonInlineTerm = termFromInlinedTypeApplyUnsafe('{scala.compiletime.summonInline}.asTerm)
          val summonInlineApp = TypeApply(summonInlineTerm, List(paramTypeclassTree))
          val instance = wrapInCallByNeedTerm(summonInlineApp, paramTypeclassTree)
          val unit = '{()}.asTerm
          val fallbackTerm = fallback.asTerm match
            case Inlined(_, _, i) => i
          val appliedFallbackTerm = TypeApply(Select(Ref(fallbackTerm.symbol), fallbackTerm.symbol.methodMember("doDerive").head), List(paramTypeTree))
          val fallbackCallByNeedTerm = wrapInCallByNeedTerm(appliedFallbackTerm, paramTypeclassTree)
          Apply(
            fun = TypeApply(
              fun = Select(
                qualifier = paramObj,
                symbol = paramConstrSymbol
              ),
              args = List(TypeTree.of[Typeclass], TypeTree.of[T], paramTypeTree)
            ),
            args = List(
              /*name =*/ Expr(paramSymbol.name).asTerm,
              /*idx =*/ Expr(idx).asTerm,
              /*repeated =*/ Expr(isRepeated(paramTypeTree.tpe)).asTerm,
              /*cbn =*/ paramTypeclassTree.tpe.asType match
                case '[p] =>
                  Expr.summon[p].map(_ => instance).getOrElse(fallbackCallByNeedTerm)
              ,
              /*defaultVal =*/ '{CallByNeed(None)}.asTerm,
              /*annotations =*/ Expr.ofList(filterAnnotations(paramSymbol.annotations).toSeq.map(_.asExpr)).asTerm,
              /*typeAnnotations =*/ Expr.ofList(filterAnnotations(getTypeAnnotations(paramTypeTree.tpe)).toSeq.map(_.asExpr)).asTerm
            )
          ).asExprOf[CaseClass.Param[Typeclass, T]]
      }
    }

  end getParamsImpl

  def getSubtypesImpl[Typeclass[_]: Type, T: Type](fallback: Expr[Derivation[Typeclass]]): Expr[List[SealedTrait.Subtype[Typeclass, T, _]]] =

    val typeSymbol = TypeRepr.of[T].typeSymbol
    val parentTypeTree = TypeTree.of[T]

    val subTypeObj = '{SealedTrait.Subtype}.asTerm
    val subTypeConstrSymbol = TypeRepr.of[SealedTrait.Subtype.type].termSymbol.declaredMethod("apply").head

    val annotations = paramAnns[T].to(Map)
    val typeAnnotations = paramTypeAnns[T].to(Map)

    Expr.ofList {
      typeSymbol.children.zipWithIndex.collect {
        case (subTypeSymbol: Symbol, idx: Int) =>
          val classDef: ClassDef = subTypeSymbol.tree.asInstanceOf[ClassDef]
          val subTypeTypeTree: TypeTree = TypeIdent(subTypeSymbol) //TODO TypeTree of classDef
          val subTypeTypeclassTree = Applied(TypeTree.of[Typeclass], List(subTypeTypeTree))
          val summonInlineTerm = termFromInlinedTypeApplyUnsafe('{scala.compiletime.summonInline}.asTerm)
          val summonInlineApp = TypeApply(summonInlineTerm, List(subTypeTypeclassTree))
          val instance = wrapInCallByNeedTerm(summonInlineApp, subTypeTypeclassTree)
          val fallbackTerm = fallback.asTerm match
            case Inlined(_, _, i) => i
          val appliedFallbackTerm = TypeApply(Select(Ref(fallbackTerm.symbol), fallbackTerm.symbol.methodMember("doDerive").head), List(subTypeTypeTree))
          val fallbackCallByNeedTerm = wrapInCallByNeedTerm(appliedFallbackTerm, subTypeTypeclassTree)
          Apply(
            fun = TypeApply(
              fun = Select(
                qualifier = subTypeObj,
                symbol = subTypeConstrSymbol
              ),
              args = List(TypeTree.of[Typeclass], TypeTree.of[T], subTypeTypeTree)
            ),
            args = List(
              /*name =*/ typeInfo(subTypeTypeTree.tpe).asTerm,
              /*annotations =*/ Expr.ofList(filterAnnotations(subTypeSymbol.annotations).toSeq.map(_.asExpr)).asTerm,
              /*typeAnnotations =*/ Expr.ofList(filterAnnotations(getTypeAnnotations(subTypeTypeTree.tpe)).toSeq.map(_.asExpr)).asTerm,
              /*isObject =*/ Expr(isObject(subTypeTypeTree.tpe)).asTerm,
              /*idx =*/ Expr(idx).asTerm,
              /*cbn =*/ subTypeTypeclassTree.tpe.asType match {
                case '[p] =>
                  Expr.summon[p].map(_ => instance).getOrElse(fallbackCallByNeedTerm)
              }
            )
          ).asExprOf[SealedTrait.Subtype[Typeclass, T, _]]
      }
    }

  end getSubtypesImpl

end DerivationImpl
