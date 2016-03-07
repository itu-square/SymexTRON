package semantics

import semantics.domains.{Instances, CMem}
import syntax.ast.Fields

/**
  * Created by asal on 07/03/2016.
  */
object DotConverter {
  def convertCMem(graphname: String, mem: CMem): String = {
    def flatRel(env: Map[Instances, Map[Fields, Set[Instances]]]) : Set[(Instances, Fields, Set[Instances])] = {
      env.flatMap { case (inst, fs) => fs.map { case (f, oinsts) => (inst, f, oinsts) } }.toSet
    }
    def instSet(oinsts: Set[Instances]): String = {
      oinsts.map(oinst => s"L$oinst").mkString("{", ";", "}")
    }
    val vars = s"""stack [shape = record label = "${mem.stack.keySet.map(v => s"<$v> $v").mkString("|")}"];"""
    val insts = mem.heap.typeenv.map { case (inst, clazz) =>
        s"""L$inst [label = "$inst : ${clazz.name}" shape = egg];"""
    }.mkString("\n|  ")
    val varvals = mem.stack.map { case (v, insts) =>
        s"""stack:$v -> ${instSet(insts)} [style = dotted];"""
    }.mkString("\n|  ")
    val children = flatRel(mem.heap.childenv).map { case (inst, f, oinsts) =>
        s"""L$inst -> ${instSet(oinsts)} [arrowtail = diamond dir = both label = $f];"""
    }.mkString("\n|  ")
    val refs = flatRel(mem.heap.refenv).map { case (inst, f, oinsts) =>
      s"""L$inst -> ${instSet(oinsts)} [style = dashed label = " $f "];"""
    }.mkString("\n|  ")
    s"""
       |digraph $graphname {
       |  $vars
       |  $insts
       |  $varvals
       |  $children
       |  $refs
       |}
     """.stripMargin
  }
}
