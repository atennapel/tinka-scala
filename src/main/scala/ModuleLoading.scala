import Common.*
import Parser.parser
import Presyntax.RTm
import Elaboration.elaborate
import Globals.{GlobalEntry, addGlobal}
import Debug.debug
import java.net.URI
import java.io.File
import scala.io.Source
import scala.collection.mutable
import parsley.io.given

import scala.annotation.tailrec

object ModuleLoading:
  private type DepMap = mutable.Map[String, Entry]
  private val urimap: DepMap = mutable.Map.empty

  private case class Entry(uri: String, tm: RTm, uris: Set[String]):
    def hasNoDeps: Boolean = uris.isEmpty
    def removeDep(x: String): Entry = Entry(uri, tm, uris - x)

  def reset(): Unit = urimap.clear()

  def load(uri0: String): String =
    val uri = transformUri(uri0)
    debug(s"load module start: $uri")
    loadUris(uri)
    toposort(urimap) match
      case Left(cycle) =>
        throw Exception(s"cycle in modules: ${cycle.mkString(", ")}")
      case Right(order) =>
        debug(s"modules to load: $order")
        order.foreach(loadUri)
        uri

  private def loadUris(uri: String): Unit =
    if !urimap.contains(uri) then
      debug(s"load uris: $uri")
      val tm = parser
        .parseFromFile(new File(transformFilename(uri)))
        .flatMap(_.toTry)
        .get
      val uris = tm.uris
      urimap.put(uri, Entry(uri, tm, uris))
      uris.filter(!urimap.contains(_)).foreach(loadUris)
      ()

  private def transformFilename(uri: String): String =
    if uri.endsWith(".tinka") then uri else s"$uri.tinka"
  private def transformUri(uri: String): String =
    if uri.endsWith(".tinka") then uri.take(uri.size - 6) else uri

  private def loadUri(uri: String): Unit =
    debug(s"load uri: $uri")
    implicit val ctx: Ctx = Ctx.empty()
    val (etm, ety) = elaborate(urimap(uri).tm)
    addGlobal(uri, GlobalEntry(uri, etm, ety, ctx.eval(etm), ctx.eval(ety)))
    debug(s"loaded uri: $uri")
    ()

  private def toposort(map: DepMap): Either[List[String], List[String]] =
    toposort(map.clone(), Nil, map.values.filter(_.hasNoDeps).toList)
      .map(_.reverse)

  @tailrec
  private def toposort(
      map: DepMap,
      l: List[String],
      es: List[Entry]
  ): Either[List[String], List[String]] = es match
    case Nil if !map.values.forall(_.hasNoDeps) =>
      Left(map.filter((_, v) => !v.hasNoDeps).keys.toList)
    case Nil => Right(l)
    case Entry(x, _, deps) :: s =>
      val dependents = map.values.filter(_.uris.contains(x)).map(_.removeDep(x))
      dependents.foreach(e => map += (e.uri -> e))
      toposort(map, x :: l, s ++ dependents.filter(_.hasNoDeps))
