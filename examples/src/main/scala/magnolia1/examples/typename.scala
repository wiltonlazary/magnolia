package magnolia1.examples

import magnolia1.{CaseClass, Magnolia, SealedTrait, TypeName}

import scala.language.experimental.macros

trait TypeNameInfo[T] {
  def name: TypeName

  def subtypeNames: Seq[TypeName]
}

object TypeNameInfo {
  type Typeclass[T] = TypeNameInfo[T]
  def join[T](ctx: CaseClass[TypeNameInfo, T]): TypeNameInfo[T] =
    new TypeNameInfo[T] {
      def name: TypeName = ctx.typeName

      def subtypeNames: Seq[TypeName] = Nil
    }

  def split[T](ctx: SealedTrait[TypeNameInfo, T]): TypeNameInfo[T] =
    new TypeNameInfo[T] {
      def name: TypeName = ctx.typeName

      def subtypeNames: Seq[TypeName] = ctx.subtypes.map(_.typeName)
    }

  def fallback[T]: TypeNameInfo[T] =
    new TypeNameInfo[T] {
      def name: TypeName = TypeName("", "Unknown Type", Seq.empty)

      def subtypeNames: Seq[TypeName] = Nil
    }

  implicit def gen[T]: TypeNameInfo[T] = macro Magnolia.gen[T]
}
