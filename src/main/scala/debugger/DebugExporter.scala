package viper.silicon.debugger

import org.jgrapht.alg.connectivity.GabowStrongConnectivityInspector
import org.jgrapht.alg.cycle.CycleDetector
import org.jgrapht.graph.{DefaultDirectedGraph, DefaultEdge}
import org.jgrapht.traverse.TopologicalOrderIterator
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.debugger.ExportUtils._
import viper.silicon.interfaces.state.Chunk
import viper.silicon.state._
import viper.silicon.state.terms.{Sort, Term, sorts}
import viper.silicon.resources
import viper.silicon.resources.{FieldID, PredicateID}
import viper.silver.ast
import viper.silver.ast.utility.Functions.{FuncName, allSubexpressions}
import viper.silver.ast.utility.Simplifier
import viper.silver.ast.{DomainAxiom, Exp, PermExp, Program}
import viper.silver.utility.Common.Rational

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Paths}
import scala.annotation.tailrec
import scala.collection.mutable.{ArrayBuffer, Set => MSet}
import scala.collection.{immutable, mutable}
import scala.io.StdIn.readLine
import scala.jdk.CollectionConverters._


// Main wrapper object
object DebugExporter {
  def exportIsabelle(obl: ProofObligation): Unit = {
    println(s"Enter a file name:")
    val userInput = readLine()
    if (userInput.equals("q") || userInput.equals("Q")) return

    try {
      val filepath = Paths.get(userInput)
      if (Files.exists(filepath)) {
        println("File already exists, overwrite? (y/n)")
        val overwrite = readLine()
        if (overwrite.equals("y") || overwrite.equals("Y")) {
          print("Overwriting file...")
        } else {
          println("Did not export")
          return
        }
      } else {
        print("Exporting to file...")
        Files.createFile(filepath)
      }

      // Write to file
      val writer = Files.newBufferedWriter(filepath, StandardCharsets.UTF_8)
      val filename = filepath.getFileName.toString.split('.')(0)
      val t = new Translator(obl, filename)
      t.translateObligation()
      t.strings.foreach(s => writer.write(s + "\n"))
      writer.close()
      print(" Success!\n")

    } catch {
      case e: Throwable =>
        println("Error exporting to Isabelle")
        throw e
    }
  }
}

// Things to rewrite as you translate terms
case class Rewrites(varRenames: immutable.Map[String, String],
                    termReplacements: immutable.Map[Term, String])

object Rewrites {
  def apply(varRenames: immutable.Map[String, String],
            termReplacements: immutable.Map[Term, String]): Rewrites = {
    new Rewrites(varRenames, termReplacements)
  }

  val emptyRewrites: Rewrites = Rewrites(Map(), Map())

  def addRename(rewrites: Rewrites, name: String, rep: String): Rewrites = {
    Rewrites(rewrites.varRenames + (name -> rep), rewrites.termReplacements)
  }

  def addRenames(rewrites: Rewrites, toAdd: Map[String, String]): Rewrites = {
    Rewrites(rewrites.varRenames ++ toAdd, rewrites.termReplacements)
  }

  def addTermReplace(rewrites: Rewrites, t: Term, rep: String): Rewrites = {
    Rewrites(rewrites.varRenames, rewrites.termReplacements + (t -> rep))
  }
}

/**
 * Translates Silver expressions and Silicon terms into Isabelle syntax.
 * Takes abstraction maps and renamings to change the translation.
 */
class Translator(val obl: ProofObligation, val filename: String) {
  var strings = ArrayBuffer[String]() // Strings to be written to .thy file
  private val program = obl.s.program
  private val domains = program.domains.filter(d => !d.name.endsWith("WellFoundedOrder"))
  private val translationOrder: Seq[(MemberSeq, Seq[MemberSeq])] = memberTranslationSequence(program)
  private val currentHeapLabel: String = obl.v.getDebugHeapLabel(obl.s).getOrElse("currentHeapMissing")

  // Maps each debug heap label to an ancestor label it's unified with, and any extra conditions on the child heap
  private val heapSourceMap: immutable.Map[String, (String, Set[ast.Exp])] = {
    def erasable(cause: HeapCause): Boolean = {
      cause match {
        case InhalePre() | ExhalePost() | EvalExp(_) | StateConsolidation() => true
        case ExecStmt(stmt) => stmt match {
          case _: ast.Unfold
          | _: ast.Fold
          | _: ast.Package
          | _: ast.Apply => true
          case _ => false
        }
        case MergeContext() | CreateLabel() => false
      }
    }

    val oldConds = obl.s.debugOldHeaps("old").branchConds.map(_._1).toSet
    @tailrec
    def sourceHeap(debugHeap: DebugHeap, currentLabel: String, currentBCs: Set[ast.Exp]): (String, Set[ast.Exp]) = {
      if (debugHeap.cause == InhalePre()) {
        val theseConds = debugHeap.branchConds.map(_._1).toSet
        ("old", theseConds -- oldConds)
      } else if (debugHeap.parentLabel == "nil")
        (currentLabel, currentBCs)
      else if (debugHeap.intermediateCause.isDefined) {
        val parentHeap = obl.s.debugOldHeaps(debugHeap.parentLabel)
        if (parentHeap.cause == debugHeap.cause) {
          val newBCs = currentBCs ++ debugHeap.branchConds.map(_._1)
          sourceHeap(parentHeap, debugHeap.parentLabel, newBCs)
        } else (currentLabel, currentBCs)
      }
      else if (erasable(debugHeap.cause)) {
        val parentHeap = obl.s.debugOldHeaps(debugHeap.parentLabel)
        val newBCs = currentBCs ++ debugHeap.branchConds.map(_._1)
        sourceHeap(parentHeap, debugHeap.parentLabel, newBCs)
      } else (currentLabel, currentBCs)
    }

    val tempMap: mutable.Map[String, (String, Set[Exp])] = mutable.Map()
    obl.s.debugOldHeaps.foreach { case (label, debugHeap) =>
      val (source, conds) = sourceHeap(debugHeap, label, debugHeap.branchConds.map(_._1).toSet)
      tempMap += (label -> (source, conds))
    }
    tempMap.toMap
  }

  private val (basicRewrites: Rewrites,
               fieldChunks: immutable.Map[Term, (BasicChunk, String)],
               predicateChunks: immutable.Map[Term, (BasicChunk, String)],
               quantFieldChunks: immutable.Map[Term, (QuantifiedFieldChunk, String)],
               quantPredChunks: immutable.Map[Term, (QuantifiedPredicateChunk, String)]) = {
    // Add local vars from the store
    val varRenames = mutable.Map[String, String]()
    for ((lVar, term) <- obl.s.g.termValues) {
      term match {
        case terms.Var(id, _, _) =>
          if (!(varRenames contains id.name)) {
            varRenames += id.name -> safeString(lVar.name) // add if non-existent
            varRenames += nameWithoutVersion(id.name) -> safeString(lVar.name)
          } else if (idHead(id) == lVar.name) {
            varRenames(id.name) = safeString(lVar.name) // update if better match found
            varRenames(nameWithoutVersion(id.name)) = safeString(lVar.name)
          }
        case _ => println(s"Store entry is not a Var: $lVar -> $term")
      }
    }
    // Add location variables from the heap
    val termReps = mutable.Map[Term, String]()
    val fields = mutable.Map[Term, (BasicChunk, String)]()
    val predicates = mutable.Map[Term, (BasicChunk, String)]()
    val quantFields = mutable.Map[Term, (QuantifiedFieldChunk, String)]()
    val qfcCounter: mutable.Map[String, Int] = mutable.Map(program.fields.map(_.name).map((_, 0)): _*)
    val quantPreds = mutable.Map[Term, (QuantifiedPredicateChunk, String)]()
    val varRewrites = Rewrites(varRenames.toMap, Map())
    for ((label, heap) <- obl.s.oldHeaps.toList.reverse) {
      for (chunk <- heap.values) {
        chunk match {
          case bc: BasicChunk =>
            bc.resourceID match {
              // If the chunk is a basic field access, add rewriting
              case resources.FieldID =>
                // TODO: Add condition if we can't decide it's positive
                if (!(termReps contains bc.snap) && permIsPositive(bc.perm)) {
                  val fieldLabelString = if (label == currentHeapLabel) bc.id.name else s"${bc.id} ${safeString(label)}"
                  termReps += bc.snap -> (fieldLabelString + " " + translateTerm(bc.args.head, rewrites = varRewrites))
                  fields += bc.snap -> (bc, label)
                }
              case resources.PredicateID =>
                if (!(termReps contains bc.snap) && permIsPositive(bc.perm)) {
                  predicates += bc.snap -> (bc, label)
                }
            }
          case qfc: QuantifiedFieldChunk =>
            if (!(quantFields contains qfc.snapshotMap)) {
              val field = qfc.id.name
              val mapLabel = s"${field}Map${qfcCounter(field)}"
              qfcCounter(field) = qfcCounter(field) + 1
              quantFields += (qfc.snapshotMap -> (qfc, mapLabel))
            }
          case qpc: QuantifiedPredicateChunk =>
            if (!(quantPreds contains qpc.snapshotMap))
              quantPreds += (qpc.snapshotMap -> (qpc, label))
          case _ =>
            println("Other chunk: " + chunk.toString)
        }
      }
    }
    (Rewrites(varRenames.toMap, termReps.toMap), fields.toMap, predicates.toMap, quantFields.toMap, quantPreds.toMap)
  }

  def translateObligation(): Unit = {
    strings += s"theory $filename\n"
    strings += "imports \"~/Viper/isabelle/ViperTranslations\"\n"
    strings += "begin\n\n"

    declareDomainTypes()
    defineFields()
    translateMembers()
    generateLemma()

    strings += "end"
  }

  private def declareDomainTypes(): Unit = {
    // First declare domain types
    if (domains.nonEmpty) {
      strings += "text \\<open>Declare domain types\\<close>\n"
      domains.foreach(d => strings += "typedecl " + d.name)
      strings += "\n"
    }
  }

  private def defineFields(): Unit = {
    if (program.fields.nonEmpty) {
      strings += "text \\<open>Declare field functions\\<close>\n"
      strings += "locale Fields ="
      val fieldLength = program.fields.map(_.name.length).max
      for (fld <- program.fields) {
        val nameString = padString(safeString(fld.name), fieldLength)
        strings += s"  fixes $nameString :: \"Heap $FN_ARR ref $FN_ARR ${translateType(fld.typ)}\""
      }
      strings += "\n"
    }
  }

  private def translateMembers(): Unit = {
    strings += "text \\<open>Translate domains, functions and predicates\\<close>\n"

    for ((mSeq, deps) <- translationOrder) {
      val depLocales = (if (heapDepMemSeq(mSeq)) "\n  Fields +" else "") +
        deps.map(m => s"\n  ${localeName(m)} +").mkString("")
      strings += s"locale ${localeName(mSeq)} =" + depLocales
      translateMemberSeq(mSeq)
      strings += ""
    }
    strings += ""
  }

  private def heapDepMemSeq(seq: MemberSeq): Boolean = {
    seq.exists {
      case DomainName(_) => false
      case FunctionName(name) => !program.findFunction(name).isPure
      case PredicateName(_) => true
    }
  }

  // Translate a single collection of inter-dependent members
  private def translateMemberSeq(memSeq: MemberSeq): Unit = {
    for (member <- memSeq) {
      member match {
        case DomainName(name) => declareDomain(program.findDomain(name))
        case FunctionName(name) => declareFunction(program.findFunction(name))
        case PredicateName(name) => declarePredicate(program.findPredicate(name))
      }
    }
    for (member <- memSeq) {
      member match {
        case DomainName(name) => defineDomain(program.findDomain(name))
        case FunctionName(name) => defineFunction(program.findFunction(name))
        case PredicateName(name) => definePredicate(program.findPredicate(name))
      }
    }
  }

  private def declareDomain(domain: ast.Domain): Unit = {
    domain.functions.foreach(fn => strings += s"  fixes " + functionType(fn))
  }

  private def defineDomain(domain: ast.Domain): Unit = {
    for (ax <- domain.axioms) {
      val axName = ax match {
        case ast.NamedDomainAxiom(name, _) => name + ": "
        case _ => ""
      }
      strings += s"  assumes $axName\"${translateExp(ax.exp)}\""
    }
  }

  private def declareFunction(fn: ast.Function): Unit = {
    strings += s"  fixes " + functionType(fn, isHeapDep = !fn.isPure)
    if (fn.pres.nonEmpty) {
      strings += s"  fixes " + functionType(fn, isPrecondition = true, isHeapDep = !fn.isPure)
    }
  }

  private def defineFunction(fn: ast.Function): Unit = {
    val argString = (if (fn.isPure) "" else "h ") + fn.formalArgs.map(_.name).mkString(" ")
    val argStringWTypes = (if (fn.isPure) "" else "(h::Heap) ") +
      fn.formalArgs.map(a => s"(${a.name}::${translateType(a.typ)})").mkString(" ")

    // Translate function body
    if (fn.body.isDefined) {
      val fnRHS = translateExp(fn.body.get)
      if (fn.pres.isEmpty) {
        strings += s"  assumes ${fn.name}_def: \"\\<And>$argString. ${fn.name} $argString \\<equiv>\n    $fnRHS\""
      } else {
        strings += s"  assumes ${fn.name}_def: \"\\<And>$argString. " +
          s"${fn.name}_pre $argString $META_ARR ${fn.name} $argString =\n    $fnRHS\""
      }
      // Translate internal function calls
      getPrecPropagationExp(fn, obl.s.program) match {
        case None =>
        case Some(exp) =>
          strings += s"  assumes ${fn.name}_calls: \"\\<And>$argStringWTypes. ${translateExp(exp)}\""
      }
    }
    // Postconditions
    if (fn.posts.nonEmpty) {
      strings += s"  assumes ${fn.name}_posts: \"\\<And>$argStringWTypes. ${fn.name}_pre $argString $META_ARR"
      val postStrings = fn.posts.map(translateExp(_, parenthesisLevel = 35, resultString = Some(s"${fn.name} $argString")))
      val combined = "    " + postStrings.mkString("\n    \\<and> ")
      strings += combined + "\""
    }
    // Framing axioms
    if (!fn.isPure) {
      val argStringH1 = "h1" + argString.drop(1)
      val argStringH2 = "h2 " + fn.formalArgs.map(_.name + "'").mkString(" ")
      val footprint = fn.pres.filter(!_.isPure).map(translateExp(_, parenthesisLevel = 35, isFrameAxiom = true)).mkString(" \\<and> ")
      strings += s"  assumes ${fn.name}_framing: \"\\<And>h1 $argStringH2. " +
        s"${fn.name}_pre $argStringH1 \\<and> ${fn.name}_pre $argStringH2"
      strings += s"    \\<and> $footprint"
      strings += s"    $META_ARR ${fn.name} $argStringH1 = ${fn.name} $argStringH2\""
    }
  }

  private def declarePredicate(pred: ast.Predicate): Unit = {
    val typeString = s"Heap $FN_ARR " + pred.formalArgs.map(a => translateType(a.typ) + s" $FN_ARR ").mkString("")
    strings += s"  fixes ${pred.name} :: \"${typeString}bool\""
    val typeTuple = s"Heap \\<times> ${pred.formalArgs.map(a => translateType(a.typ)).mkString(" \\<times> ")}"
    strings += s"  fixes ${pred.name}_eq :: \"$typeTuple $FN_ARR $typeTuple $FN_ARR bool\""
  }

  private def definePredicate(pred: ast.Predicate): Unit = {
    pred.getPureFragment match {
      case Some(exp) =>
        val argString = "h " + pred.formalArgs.map(_.name).mkString(" ")
        val bodyString = translateExp(exp, parenthesisLevel = 51)
        strings += s"  assumes unfold_${pred.name}: \"\\<And>$argString. " +
          s"${pred.name} $argString $META_ARR\n    $bodyString\""
      case None =>
    }
    pred.getAccessFragment match {
      case Some(exp) =>
        val varsString = "h h' " + pred.formalArgs.map(a => s"${a.name} ${a.name}'").mkString(" ")
        val argString1 = s"(h, ${pred.formalArgs.map(_.name).mkString(", ")})"
        val argString2 = s"(h', ${pred.formalArgs.map(_.name + "'").mkString(", ")})"
        val bodyString = translateExp(exp, parenthesisLevel = 51, isFrameAxiom = true)
        strings += s"  assumes ${pred.name}_eq_def: \"\\<And>$varsString. ${pred.name}_eq $argString1 $argString2 $META_ARR"
        strings += s"    $bodyString\""
      case None =>
    }
  }

  // returns "fn_name :: args* => result", with optional _pre suffix, and heap argument
  private def functionType(fn: ast.FuncLike, isPrecondition: Boolean = false, isHeapDep: Boolean = false): String = {
    val name = if (isPrecondition) fn.name + "_pre" else fn.name
    val maybeHeap = if (isHeapDep) s"Heap $FN_ARR " else ""
    val argString = fn.formalArgs.map(a => translateType(a.typ) + s" $FN_ARR ").mkString("")
    val typeString = if (isPrecondition) "bool" else translateType(fn.typ)
    name + " :: \"" + maybeHeap + argString + typeString + "\""
  }

  private def generateLemma(): Unit = {
    strings += "text \\<open>Proof obligation\\<close>\n"
    strings += "locale Program ="
    if (program.fields.nonEmpty) strings += "  Fields +"
    strings += translationOrder.map { case (mSeq, _) => s"  ${localeName(mSeq)}" }.mkString(" +\n")
    strings += "\ncontext Program\nbegin\n\nlemma"
    translateStore()
    translateHeaps()
    strings += "  (* Assumptions *)"
    obl.assumptionsExp.foreach(translateDebugExp(_))

    // val assertionTerm = obl.eAssertion.term.getOrElse(obl.assertion)
    strings += "  (* Proof goal *)"
    obl.eAssertion.finalExp match {
      case Some(exp) => strings += "  shows \"" + translateExp(exp) + "\""
      case None => strings += "  shows \"" + translateTerm(obl.assertion) + "\""
    }
    strings += "  (* Complete proof here *)\n  sorry\n"
    strings += "end\n"
  }

  private def translateStore(): Unit = {
    strings += "  (* Local variables *)"
    for ((v, (t, _)) <- obl.s.g.values) {
        strings += s"  fixes ${safeString(v.name)} :: \"${translateSort(t.sort)}\""
    }
  }

  private def translateHeaps(): Unit = {
    val keyLabels = heapSourceMap.values.map(_._1).toSet
    val keyHeaps = obl.s.debugOldHeaps.filter(keyLabels contains _._1)

    /*
    val groupedHeaps = heapSourceMap.groupMap(_._2._1) {
      case (childLabel, (_, conds)) => (childLabel, conds)
    }
    for ((parentHeap, children) <- groupedHeaps) {
      val chunkList = children.flatMap {
        case (childLabel, cond) => obl.s.debugOldHeaps(childLabel).heap.values.map((_, cond))
      }.toList.distinct.zipWithIndex

      // TODO: Maybe explicitly identify current heap?
      strings += s"  (* Heap $parentHeap *)"
      for (((chunk, conds), idx) <- chunkList) {
        translateChunk(chunk, conds, parentHeap, idx)
      }
    }
    */
    for ((label, dh) <- keyHeaps) {
      strings += s"  (* Heap $label *)"
      for ((chunk, idx) <- dh.heap.values.zipWithIndex) {
        translateChunk(chunk, Set(), label, idx)
      }
    }
  }

  private def translateChunk(c: Chunk, conditions: Set[ast.Exp], heapLabel: String, idx: Int): Unit = {
    def fieldSnapInOtherHeap(s: Term): Boolean = (fieldChunks contains s) && fieldChunks(s)._2 != heapLabel
    def predSnapInOtherHeap(s: Term): Boolean = (predicateChunks contains s) && predicateChunks(s)._2 != heapLabel
    val condString = conditions.map(translateExp(_)).mkString(" \\<and> ")

    c match {
      case bc: BasicChunk =>
        bc.resourceID match {
          case FieldID =>
            assert(bc.args.length == 1, "Method translateChunk expected FieldChunk to have exactly one arg.")
            if (fieldSnapInOtherHeap(bc.snap)) {
              val ref = translateTerm(bc.args.head, parenthesisLevel = 100)
              val permCondition = permCondSimp(bc.perm)
              val condString = if (permCondition == terms.True) "" else translateTerm(permCondition) + s" $META_ARR "
              val field = s"${bc.id.name}' ${safeString(heapLabel)} $ref"
              val chunk = s"$condString$field = ${translateTerm(bc.snap)}"
              strings += s"  assumes ${safeString(heapLabel)}_$idx: \"$chunk\""
            } // TODO: Should we add something here if only
          case PredicateID =>
            val chunkString = safeString(bc.id.name) + s" ${safeString(heapLabel)} " +
              bc.args.map(translateTerm(_, parenthesisLevel = 100)).mkString(" ")
            val predEq = if (predSnapInOtherHeap(bc.snap)) {
              val (otherChunk, otherLabel) = predicateChunks(bc.snap)
              val thisTuple = s"(${safeString(heapLabel)}, ${bc.args.map(translateTerm(_)).mkString(", ")})"
              val otherTuple = s"(${safeString(otherLabel)}, ${otherChunk.args.map(translateTerm(_)).mkString(", ")})"
              s" \\<and> ${bc.id.name}_eq $thisTuple $otherTuple"
            } else ""
            strings += s"  assumes ${safeString(heapLabel)}_$idx: \"$chunkString$predEq\""
        }
      case qfc: QuantifiedFieldChunk =>
        // TODO: You can only have one reciever, which I think is qfc.invs.get.invertibleExps.get.head
        // val rcvr = translateExp(qfc.invs.get.invertibleExps.get.head, parenthesisLevel = 100)
        val rcvr = qfc.singletonRcvrExp match {
          case Some(e) => translateExp(e, parenthesisLevel = 100)
          case None => (for (inv <- qfc.invs; exps <- inv.invertibleExps; e <- exps.headOption)
            yield translateExp(e, parenthesisLevel = 100)).getOrElse("missingInvExp")
        }
        // qfc.quantifiedVarExps.get.zip(qfc.invs.get.invertibleExps.get).map(v => s"${v._1.name} == ${simplify(v._2)}").mkString(" && ")
        val field = s"${qfc.id.name} ${safeString(heapLabel)} r"
        if (qfc.conditionExp.isDefined && qfc.permExp.isDefined) {
          val permCondition = Simplifier.simplify(ast.And(qfc.conditionExp.get, permCondSimpExp(qfc.permExp.get))())
          val condString = translateExp(permCondition) + s" $META_ARR"
          val expVars = qfc.invs.map(_.qvarExps.getOrElse(Seq())).getOrElse(Seq())
          val varString = expVars.map(v => s" (${safeString(v.name)}::${translateType(v.typ)})").mkString("")
          val chunk = quantFieldChunks.get(qfc.fvf) match {
            case Some((_, mapLabel)) => s"\\<And>r$varString. $condString $field = $mapLabel $rcvr"
            case None => s"\\<And>r. $condString $field = ${qfc.id}_${translateTerm(qfc.fvf)} $rcvr"
          }
          strings += s"  assumes ${safeString(heapLabel)}_$idx: \"$chunk\""
        } else {
          val permCondition = terms.And(qfc.condition, permCondSimp(qfc.permValue))
          val condString = translateTerm(permCondition) + s" $META_ARR"
          val chunk = quantFieldChunks.get(qfc.fvf) match {
            case Some((_, mapLabel)) => s"\\<And>r. $condString $field = $mapLabel r"
            case None => s"\\<And>r. $condString $field = ${qfc.id}_${translateTerm(qfc.fvf)} r"
          }
          strings += s"  assumes ${safeString(heapLabel)}_$idx: \"$chunk\""
        }
      case qpc: QuantifiedPredicateChunk =>
        val condString = translateTerm(terms.And(qpc.condition, permCondSimp(qpc.permValue)))
        val argList = qpc.quantifiedVars.map(_.id.name)
        val quantifyString = "\\<And>" + argList.mkString(" ")
        val predString = s"$quantifyString. $condString $META_ARR ${qpc.id.name} ${safeString(heapLabel)} ${argList.mkString(" ")}"
        strings += s"  assumes ${safeString(heapLabel)}_${idx}a: \"$predString\""
        if (predSnapInOtherHeap(qpc.snapshotMap)) {
          val (otherChunk, otherLabel) = predicateChunks(qpc.snapshotMap)
          val thisTuple = s"($heapLabel, ${argList.mkString(", ")})"
          val otherTuple = s"($otherLabel, ARGS???)"
          val eqString = s"${qpc.id.name}(args) \\<and> ${qpc.id.name}_eq $thisTuple $otherTuple"
          strings += s"  assumes ${safeString(heapLabel)}_${idx}b: \"$condString $META_ARR $eqString\""
        }
    }

  }

  case class TranslationOptions(parenthesisLevel: Int,
                                collapseSnaps: Boolean,
                                annotateIntLits: Boolean) {
    def collapseSnapsOn(): TranslationOptions = this.copy(collapseSnaps = true)
    def annotateIntLitsOff(): TranslationOptions = this.copy(annotateIntLits = false)
  }

  object TranslationOptions {
    def apply(parenthesisLevel: Int,
              collapseSnaps: Boolean,
              annotateIntLits: Boolean): TranslationOptions = new TranslationOptions(parenthesisLevel,
      collapseSnaps,
      annotateIntLits)
  }

  val defaultOptions = TranslationOptions(parenthesisLevel = 0, collapseSnaps = false, annotateIntLits = true)

  // Main translation function
  private def translateTerm(term: Term,
                            parenthesisLevel: Int = 0,
                            rewrites: Rewrites = basicRewrites,
                            options: TranslationOptions = defaultOptions): String = {
    // Recursive call, for convenience
    def rec(term2: Term, pLevel: Int, ops: TranslationOptions = options): String = translateTerm(term2, pLevel, rewrites, options)
    def wrap(s: String, pLevel: Int): String = if (pLevel <= parenthesisLevel) s"($s)" else s
    def recOp(left: Term, op: String, right: Term, pLevel: Int): String = {
      wrap(rec(left, pLevel) + s" $op " + rec(right, pLevel), pLevel)
    }

    if (rewrites.termReplacements contains term) {
      return wrap(rewrites.termReplacements(term), 100)
    } // else

    term match {
      // Functions and Applications
      case terms.Var(id, _, _) => rewrites.varRenames getOrElse(id.name, safeId(id))
      case terms.Let(bindings, body) =>
        val bindString = bindings.transform((bVar, bTerm) => rec(bVar, 10) + " = " + rec(bTerm, 10)).mkString("; ")
        wrap(s"let $bindString in ${rec(body, 10)}", 10)
      case terms.Null => "Null"
      case terms.Unit => "UNIT"
      case terms.App(applicable, args, heapLabel) =>
        // TODO: if it is spurious precondition then remove it
        val og_fn = applicable.id.name.takeWhile(_ != '%')
        obl.s.program.findFunctionOptionally(og_fn) match {
          case None => safeId(applicable.id) + args.map(" " + rec(_, 100)).mkString("")
          case Some(f) =>
            if (applicable.id.name.contains("%precondition") && f.pres.isEmpty) "True"
            else if (f.isPure) s"${safeId(applicable.id)}" + args.tail.map(" " + rec(_, 100)).mkString("")
            else s"${safeId(applicable.id)} ${safeString(heapLabel.getOrElse("NO_HEAP"))} " + args.tail.map(rec(_, 100)).mkString(" ")
        }
      // Stuff
      case terms.IntLiteral(i) => if (options.annotateIntLits) s"($i::int)" else i.toString()
      case b: terms.BooleanLiteral => b.toString
      case terms.Quantification(q, vars, body, _, _, _, _) =>
        val varString = vars.map(v =>
          if (rewrites.varRenames.contains(v.id.name)) rewrites.varRenames(v.id.name)
          else safeId(v.id) // TODO: use get or else?
        ).mkString(" ")
        wrap(s"${quantifierToString(q)}$varString. ${rec(body, 10)}", 10)
      // Arithmetic
      case terms.Plus(left, right) => recOp(left, "+", right, 65)
      case terms.Minus(left, right) => recOp(left, "-", right, 65)
      case terms.Times(left, right) => recOp(left, "*", right, 70)
      case terms.Div(left, right) => recOp(left, "div", right, 70)
      case terms.Mod(left, right) => recOp(left, "mod", right, 70)
      // Logic
      case terms.Not(t) => t match {
        case terms.BuiltinEquals(left, right) => recOp(left, "\\<noteq>", right, 50)
        case terms.CustomEquals(left, right) => recOp(left, "\\<noteq>", right, 50)
        case terms.SeqIn(seq, elem) => recOp(elem, "\\<notin>:", seq, 51)
        case terms.SetIn(elem, set) => recOp(elem, "\\<notin>\\<^sup>+", set, 51)
        case _ => wrap("\\<not>" + rec(t, 40), 40)
      }
      case terms.Or(subterms) => subterms.map(rec(_, 30)).mkString(" \\<or> ") //seqOpToString(subterms, "\\<or>")
      case terms.And(subterms) => subterms.map(rec(_, 35)).mkString(" \\<and> ")
      case terms.Implies(left, right) => recOp(left, "\\<longrightarrow>", right, 25)
      case terms.Iff(left, right) => recOp(left, "\\<longleftrightarrow>", right, 25)
      case terms.Ite(t0, t1, t2) => wrap(s"if ${rec(t0, 10)} then ${rec(t1, 10)} else ${rec(t2, 10)}", 10)
      case terms.BuiltinEquals(left, right) => recOp(left, "=", right, 50)
      case terms.CustomEquals(left, right) => recOp(left, "=", right, 50)
      //Comparison
      case terms.Less(left, right) => recOp(left, "<", right, 51)
      case terms.AtMost(left, right) => recOp(left, "\\<le>", right, 51)
      case terms.Greater(left, right) => recOp(left, ">", right, 51)
      case terms.AtLeast(left, right) => recOp(left, "\\<ge>", right, 51)
      // Permissions
      case terms.NoPerm => "(0::perm)"
      case terms.FullPerm => "(1::perm)"
      case terms.FractionPermLiteral(r) => r.toString
      case terms.PermTimes(p0, p1) => recOp(p0, "*", p1, 70)
      case terms.IntPermTimes(p0, p1) => s"${rec(p0, 70)} * ${rec(p1, 70, options.annotateIntLitsOff())}"
      case terms.PermIntDiv(p0, p1) => s"${rec(p0, 70)} / ${rec(p1, 70, options.annotateIntLitsOff())}"
      case terms.PermPermDiv(p0, p1) => recOp(p0, "/", p1, 70)
      case terms.PermPlus(p0, p1) => recOp(p0, "+", p1, 65)
      case terms.PermMinus(p0, p1) => recOp(p0, "-", p1, 65)
      case terms.PermLess(p0, p1) => recOp(p0, "<", p1, 51)
      case terms.PermMin(p0, p1) => wrap(s"min ${rec(p0, 100)} ${rec(p1, 100)}", 100)
      // Sequences
      case terms.SeqRanged(from, to) => "[" + rec(from, 0) + ".." + rec(to, 0) + "]"
      case terms.SeqNil(_) => "[]" // Note: not using sort, maybe add type annotation
      case terms.SeqSingleton(elem) => "[" + rec(elem, 0) + "]"
      case terms.SeqAppend(left, right) => wrap(rec(left, 65) + "@" + rec(right, 65), 65)
      case terms.SeqDrop(seq, n) => wrap(s"drop\\<^sub>Z ${rec(n, 100)} ${rec(seq, 100)}", 100)
      case terms.SeqTake(seq, n) => wrap(s"take\\<^sub>Z ${rec(n, 100)} ${rec(seq, 100)}", 100)
      case terms.SeqLength(seq) => wrap("length\\<^sub>Z " + rec(seq, 100), 100)
      case terms.SeqAt(seq, idx) => recOp(seq, "!\\<^sub>Z", idx, 100)
      case terms.SeqIn(seq, elem) => recOp(elem, "\\<in>:", seq, 51)
      case terms.SeqInTrigger(_, _) => "error: SeqInTrigger"
      case terms.SeqUpdate(seq, idx, value) => wrap(s"list_update ${rec(seq, 100)} ${rec(idx, 100)} ${rec(value, 100)}", 100)
      // Sets
      case terms.EmptySet(_) => "{||}"
      case terms.SingletonSet(elem) => s"{|${rec(elem, 0)}|}"
      case terms.SetAdd(left, right) => wrap(s"finsert ${rec(right, 100)} ${rec(left, 100)}", 100)
      case terms.SetUnion(left, right) => recOp(left, "|\\<union>|", right, 65)
      case terms.SetIntersection(left, right) => recOp(left, "|\\<inter>|", right, 70)
      case terms.SetSubset(left, right) => recOp(left, "|\\<subset>|", right, 75)
      case terms.SetDisjoint(left, right) => wrap(s"fdisjnt ${rec(left, 100)} ${rec(right, 100)}", 100)
      case terms.SetDifference(left, right) => recOp(left, "-", right, 65)
      case terms.SetIn(elem, set) => recOp(elem, "|\\<in>|", set, 51)
      case terms.SetCardinality(set) => wrap(s"card\\<^sub>Z ${rec(set, 100)}", 100)
      // Multisets
      case terms.EmptyMultiset(_) => "{#}"
      case terms.SingletonMultiset(elem) => s"{#${rec(elem, 0)}#}"
      case terms.MultisetAdd(_, _) => "error: multiset add"
      case terms.MultisetUnion(left, right) => recOp(left, "+", right, 65)
      case terms.MultisetCardinality(mset) => wrap(s"size\\<^sub>Z ${rec(mset, 100)}", 100)
      case terms.MultisetCount(mset, elem) => wrap(s"count\\<^sub>Z ${rec(mset, 100)} ${rec(elem, 100)}", 100)
      // Maps
      // TODO: Use HOL-Finite_Map instead, fix everything
      case terms.EmptyMap(keySort, valueSort) => wrap(s"fmempty::(${translateSort(keySort)}, ${translateSort(valueSort)}) fmap", 1)
      case terms.MapLookup(base, key) => wrap(rec(base, 100) + "@@" + rec(key, 100), 100)
      case terms.MapCardinality(map) => wrap("fmap_card " + rec(map, 100), 100)
      case terms.MapUpdate(map, key, value) => rec(map, 100) + "(" + rec(key, 100) + "\\<mapsto>" + rec(value, 100) + ")"
      case terms.MapDomain(map) => wrap(s"fmdom ${rec(map, 100)}", 100)
      case terms.MapRange(map) => wrap(s"fmran ${rec(map, 100)}", 100)
      // Snapshots
      case terms.Combine(_, _) => "undefined"
      case terms.First(snap) => if (options.collapseSnaps) rec(snap, parenthesisLevel) else "F" + rec(snap, parenthesisLevel)
      case terms.Second(snap) => if (options.collapseSnaps) rec(snap, parenthesisLevel) else "S" + rec(snap, parenthesisLevel)
      // Quantified Permissions
      case terms.Lookup(field, fvf, at) =>
        if (options.collapseSnaps) wrap(s"$field' ${rec(fvf, 100)} ${rec(at, 100)}", 100)
        else s"${field}_${rec(fvf, 0)} ${rec(at, 100)}"
      case terms.PermLookup(field, pm, at) => "undefined"
      case terms.Domain(field, fvf) => wrap(s"fvf_domain ${field}_${rec(fvf, 0)}", 100)
      case terms.HasDomain(field, fvf, _) => wrap(s"has_domain ${field}_${rec(fvf, 100)}", 100)
      case _: terms.FieldTrigger
           | _: terms.PredicateLookup
           | _: terms.PredicatePermLookup
           | _: terms.PredicateDomain
           | _: terms.HasPredicateDomain
           | _: terms.PredicateTrigger => "undefined"
      // Magic Wands
      case terms.MagicWandSnapshot(_) => "undefined"
      case terms.MWSFLookup(_) => "undefined"
      case terms.MagicWandChunkTerm(_) => "undefined"
      // Miscellaneous
      case terms.SortWrapper(t, _) => rec(t, parenthesisLevel)
      case terms.Distinct(_) => "undefined"
      case _ => "NOT SUPPORTED: " + term.getClass.toString + "; " + term.toString
    }
  }

  private def setOrMSetOp(s: String, t: ast.Type): String = {
    t match {
      case _: ast.SetType => s"|$s|"
      case _: ast.MultisetType => s"$s#"
    }
  }

  private def translateExp(e: Exp,
                           parenthesisLevel: Int = 0,
                           isFrameAxiom: Boolean = false,
                           variablePrime: Boolean = false,
                           resultString: Option[String] = None,
                           oldHeapLabel: Option[String] = None): String = {
    def rec(e2: Exp, pLevel: Int): String = translateExp(e2, pLevel, isFrameAxiom, variablePrime, resultString, oldHeapLabel)
    def wrap(s: String, pLevel: Int): String = if (pLevel <= parenthesisLevel) s"($s)" else s
    def recOp(left: Exp, op: String, right: Exp, pLevel: Int): String = {
      wrap(rec(left, pLevel) + s" $op " + rec(right, pLevel), pLevel)
    }

    e match {
      case ast.Add(left, right) => recOp(left, "+", right, 65)
      case ast.Sub(left, right) => recOp(left, "-", right, 65)
      case ast.Mul(left, right) => recOp(left, "*", right, 70)
      case ast.Div(left, right) => recOp(left, "div", right, 70)
      case ast.Mod(left, right) => recOp(left, "mod", right, 70)
      case ast.LtCmp(left, right) => recOp(left, "<", right, 51)
      case ast.LeCmp(left, right) => recOp(left, "\\<le>", right, 51)
      case ast.GtCmp(left, right) => recOp(left, ">", right, 51)
      case ast.GeCmp(left, right) => recOp(left, "\\<ge>", right, 51)
      case ast.EqCmp(left, right) => recOp(left, "=", right, 50)
      case ast.NeCmp(left, right) => recOp(left, "\\<noteq>", right, 50)

      case ast.IntLit(i) => i.toString()
      case ast.Minus(exp) => wrap("-" + rec(exp, 80), 80)
      case ast.Or(left, right) => recOp(left, "\\<or>", right, 30)
      case ast.And(left, right) =>
        if (isFrameAxiom && left.isPure) rec(right, parenthesisLevel)
        else if (isFrameAxiom && right.isPure) rec(left, parenthesisLevel)
        else rec(left, 35) + " \\<and> " + rec(right, 35)
      case ast.Implies(left, right) =>
        val translation = translateExp(left, parenthesisLevel, isFrameAxiom = false, variablePrime, resultString) +
          " \\<longrightarrow> " + rec(right, 25)
        wrap(translation, 25)
      case ast.MagicWand(left, right) => rec(left, 50) + " \\<longrightarrow> " + rec(right, 50) // TODO: remove?
      case ast.Not(exp) => wrap("\\<not>" + rec(exp, 40), 40)
      case ast.TrueLit() => "True"
      case ast.FalseLit() => "False"
      case ast.NullLit() => "Null"
      case ast.FieldAccessPredicate(loc, _) =>
        if (isFrameAxiom) {
          val loc1 = rec(loc.rcv, 100)
          val loc2 = translateExp(loc.rcv, 100, isFrameAxiom, variablePrime = true, resultString)
          s"${loc.field.name} h $loc1 = ${loc.field.name} h' $loc2"
        }
        else "undefined"
      case ast.PredicateAccessPredicate(loc, _) =>
        if (isFrameAxiom){
          val argString1 = loc.args.map(rec(_, 100)).mkString(", ")
          val argString2 = loc.args.map(
            translateExp(_, parenthesisLevel, isFrameAxiom, variablePrime = true, resultString)
          ).mkString(", ")
          s"${loc.predicateName}_eq (h, $argString1) (h', $argString2)"
        } else {
          val argString = loc.args.map(rec(_, 100)).mkString(" ")
          wrap(s"${loc.predicateName} h $argString", 100)
        }

      case ast.FuncApp(funcname, args) =>
        // Add implicit heap argument for heap-dep functions
        val og_fn = funcname.takeWhile(_ != '%')
        val maybeHeap = obl.s.program.findFunctionOptionally(og_fn) match {
          case None => ""
          case Some(fn) => if (fn.isPure) "" else " " + safeString(oldHeapLabel.getOrElse("h"))
        }
        wrap(safeString(funcname) + maybeHeap + args.map(a => " " + rec(a, 100)).mkString(""), 100)
      case ast.DomainFuncApp(funcname, args, _) =>
        wrap(funcname + " " + args.map(rec(_, 100)).mkString(" "), 100)
      case ast.FieldAccess(rcv, field) =>
        val heapString = (for (oldLabel <- oldHeapLabel; keyLabel <- heapSourceMap.get(oldLabel.takeWhile(_ != '#')))
          yield safeString(keyLabel._1)).getOrElse("h")
          wrap(s"${field.name} $heapString ${rec(rcv, 100)}", 100)

      case ast.CondExp(cond, thn, els) => "(if " + rec(cond, 10) + " then " + rec(thn, 10) +
        " else " + rec(els, 10) + ")"
      case ast.Unfolding(_, body) => rec(body, parenthesisLevel)
      case ast.Asserting(_, body) => rec(body, parenthesisLevel)
      case ast.Old(exp) => translateExp(exp, parenthesisLevel, isFrameAxiom, variablePrime, resultString, Some("old"))
      case ast.LabelledOld(exp, oldLabel) =>
        translateExp(exp, parenthesisLevel, isFrameAxiom, variablePrime, resultString, Some(oldLabel))
      case ast.DebugLabelledOld(exp, oldLabel) =>
        translateExp(exp, parenthesisLevel, isFrameAxiom, variablePrime, resultString, Some(oldLabel))
      case ast.Let(variable, exp, body) =>
        s"let ${safeString(variable.name)} = ${rec(exp, 10)} in ${rec(body, 10)}"
      case ast.Forall(variables, _, exp) =>
        wrap("\\<forall>" + variables.map(v => safeString(v.name)).mkString(" ") + ". " + rec(exp, 10), 10)
      case ast.Exists(variables, _, exp) =>
        wrap("\\<exists>" + variables.map(v => safeString(v.name)).mkString(" ") + ". " + rec(exp, 10), 10)
      case ast.LocalVar(name, _) =>
        if (variablePrime) safeString(name) + "'" else basicRewrites.varRenames.getOrElse(name, safeString(name))
      case ast.Result(_) => wrap(resultString.getOrElse("result"), 100)
      case ast.LocalVarWithVersion(name, _) =>
        if (variablePrime) safeString(name) + "'" else basicRewrites.varRenames.getOrElse(name, safeString(name))

      case ast.EmptySeq(_) => "[]"
      case ast.ExplicitSeq(elems) => "[" + elems.map(rec(_, 0)).mkString(", ") + "]"
      case ast.RangeSeq(low, high) => s"[${rec(low, 0)}..${rec(high, 0)}]"
      case ast.SeqAppend(left, right) => recOp(left, "@", right, 65)
      case ast.SeqIndex(s, idx) => recOp(s, "!\\<^sub>Z", idx, 100)
      case ast.SeqTake(s, n) => wrap("take\\<^sub>Z " + rec(n, 100) + " " + rec(s, 100), 100)
      case ast.SeqDrop(s, n) => wrap("drop\\<^sub>Z " + rec(n, 100) + " " + rec(s, 100), 100)
      case ast.SeqContains(elem, s) => recOp(elem, "\\<in>:", s, 51)
      case ast.SeqUpdate(s, idx, elem) => wrap(s"list_update\\<^sub>Z ${rec(s, 100)} ${rec(idx, 100)} ${rec(elem, 100)}", 100)
      case ast.SeqLength(s) => wrap("length\\<^sub>Z " + rec(s, 100), 100)

      case ast.EmptySet(_) => "{||}"
      case ast.ExplicitSet(elems) => "{|" + elems.map(rec(_, 0)).mkString(", ") + "|}"
      case ast.EmptyMultiset(_) => "{#}"
      case ast.ExplicitMultiset(elems) => "{#" + elems.map(rec(_, 0)).mkString(", ") + "#}"
      case ast.AnySetUnion(left, right) => left.typ match {
          case _: ast.SetType => recOp(left, "|\\<union>|", right, 65)
          case _: ast.MultisetType => recOp(left, "+", right, 65)
        }
      case ast.AnySetIntersection(left, right) => recOp(left, setOrMSetOp("\\<inter>", left.typ), right, 70)
      case ast.AnySetSubset(left, right) => recOp(left, setOrMSetOp("\\<subset>", left.typ), right, 75)
      case ast.AnySetMinus(left, right) => recOp(left, "-", right, 65)
      case ast.AnySetContains(elem, s) => recOp(elem, setOrMSetOp("\\<in>", s.typ), s, 51)
      case ast.AnySetCardinality(s) =>
        s.typ match {
          case _: ast.SetType => wrap("card\\<^sub>Z " + rec(s, 100), 100)
          case _: ast.MultisetType => wrap("size\\<^sub>Z " + rec(s, 100), 100)
        }

      case ast.EmptyMap(keyType, valueType) => wrap(s"fmempty::(${translateType(keyType)}, ${translateType(valueType)}) fmap", 1)
      case ast.ExplicitMap(elems) => "" //TODO
      case ast.Maplet(key, value) => s"[${rec(key, 0)}\\<mapsto>${rec(value, 0)}]\\<^sup>+"
      case ast.MapUpdate(base, key, value) => wrap(s"fmupd ${rec(key, 100)} ${rec(value, 100)} ${rec(base, 100)}", 100)
      case ast.MapContains(key, base) => recOp(key, "\\<in>m", base, 46)
      case ast.MapCardinality(base) => wrap("fmap_card " + rec(base, 100), 100)
      case ast.MapDomain(base) => wrap("fmdom " + rec(base, 100), 100)
      case ast.MapRange(base) => wrap("fmran " + rec(base, 100), 100)

      case todo => "TODO: " + todo.toString
    }
  }

  // Some custom logic for terms that can be partially filtered
  private def filterPure(term: Term): Option[Term] = {
    term match {
      case t: terms.Quantification =>
        val filteredBody = filterPure(t.body)
        if (filteredBody.isDefined) Some(t.copy(body = filteredBody.get)) else None
      case terms.And(ts) =>
        val pure = ts.flatMap(filterPure)
        if (pure.isEmpty) None else Some(terms.And(pure))
      case t => Some(t).filter(isPure)
    }
  }

  def isPure(term: Term): Boolean = {
    term match {
      case _: terms.Var => true
      // Functions and Applications
      case terms.Let(bindings, body) => bindings.forall(vt => isPure(vt._2)) && isPure(body)
      case terms.Null => true
      case terms.Unit => false
      //case terms.HeapDepApp(_, _, _) => true
      case terms.App(_, _, _) => true
      // Stuff
      case _: terms.IntLiteral => true
      case _: terms.BooleanLiteral => true
      case t: terms.Quantification => isPure(t.body)
      // Arithmetic
      case terms.Plus(left, right) => isPure(left) && isPure(right)
      case terms.Minus(left, right) => isPure(left) && isPure(right)
      case terms.Times(left, right) => isPure(left) && isPure(right)
      case terms.Div(left, right) => isPure(left) && isPure(right)
      case terms.Mod(left, right) => isPure(left) && isPure(right)
      // Logic
      case terms.Not(p) => isPure(p)
      case terms.Or(ts) => ts.forall(isPure)
      case terms.And(ts) => ts.forall(isPure)
      case terms.Implies(left, right) => isPure(left) && isPure(right)
      case terms.Iff(left, right) => isPure(left) && isPure(right)
      case terms.Ite(t0, t1, t2) => isPure(t0) && isPure(t1) && isPure(t2)
      case terms.BuiltinEquals(left, right) => isPure(left) && isPure(right)
      case terms.CustomEquals(left, right) => isPure(left) && isPure(right)
      //Comparison
      case terms.Less(left, right) => isPure(left) && isPure(right)
      case terms.AtMost(left, right) => isPure(left) && isPure(right)
      case terms.Greater(left, right) => isPure(left) && isPure(right)
      case terms.AtLeast(left, right) => isPure(left) && isPure(right)
      // Sequences
      case terms.SeqRanged(p0, p1) => isPure(p0) && isPure(p1)
      case _: terms.SeqNil => true
      case terms.SeqSingleton(e) => isPure(e)
      case terms.SeqAppend(left, right) => isPure(left) && isPure(right)
      case terms.SeqDrop(seq, n) => isPure(seq) && isPure(n)
      case terms.SeqTake(seq, n) => isPure(seq) && isPure(n)
      case terms.SeqLength(seq) => isPure(seq)
      case terms.SeqAt(seq, idx) => isPure(seq) && isPure(idx)
      case terms.SeqIn(seq, elem) => isPure(seq) && isPure(elem)
      case _: terms.SeqInTrigger => false
      case terms.SeqUpdate(seq, idx, value) => isPure(seq) && isPure(idx) && isPure(value)
      // Sets
      case _: terms.EmptySet => true
      case terms.SingletonSet(elem) => isPure(elem)
      case terms.SetAdd(left, right) => isPure(left) && isPure(right)
      case terms.SetUnion(left, right) => isPure(left) && isPure(right)
      case terms.SetIntersection(left, right) => isPure(left) && isPure(right)
      case terms.SetSubset(left, right) => isPure(left) && isPure(right)
      case terms.SetDisjoint(left, right) => isPure(left) && isPure(right)
      case terms.SetDifference(left, right) => isPure(left) && isPure(right)
      case terms.SetIn(elem, set) => isPure(elem) && isPure(set)
      case terms.SetCardinality(set) => isPure(set)
      // Multisets
      case _: terms.EmptyMultiset => true
      case terms.SingletonMultiset(elem) => isPure(elem)
      case terms.MultisetAdd(s, elem) => isPure(s) && isPure(elem)
      /*
      case terms.MultisetUnion(left, right) => isPure(left) && isPure(right)
      case terms.MultisetCardinality(mset) => "size\\<^sub>Z " + maybeBracket(mset)
      case terms.MultisetCount(mset, elem) => "count\\<^sub>Z " + maybeBracket(mset) + " " + maybeBracket(elem)
      // Maps
      case terms.EmptyMap(_, _) => "Map.empty"
      case terms.MapLookup(base, key) => maybeBracket(base) + "@@" + maybeBracket(key)
      case terms.MapCardinality(map) => "card\\<^sub>Z (dom " + maybeBracket(map) + ")"
      case terms.MapUpdate(map, key, value) => maybeBracket(map) + "(" + rec(key) + "\\<mapsto>" + rec(value) + ")"
      case terms.MapDomain(map) => "dom " + maybeBracket(map)
      case terms.MapRange(map) => "ran " + maybeBracket(map)
       */
      // Snapshots
      case _: terms.Combine => true
      case t: terms.First => true
      case t: terms.Second => true
      // Quantified Permissions
      case _: terms.Lookup => true
      case _: terms.PermLookup => false

      // Domains
      // TODO: Finish
      case _: terms.Domain => false
      case _: terms.HasDomain => false
      case _: terms.FieldTrigger => false
      // Magic Wands
      // TODO
      case _: terms.SortWrapper => true

      case _ => false
    }
  }

  private lazy val freeVars: InsertionOrderedSet[terms.Var] = {
    def deToVars(de: DebugExp): InsertionOrderedSet[terms.Var] = {
      if (de.term.isDefined) {
        de.term.get.freeVariables ++ de.children.flatMap(deToVars)
      } else {
        de.children.flatMap(deToVars)
      }
    }

    obl.assumptionsExp.flatMap(deToVars)
  }

  // Maps from variable ids to strings that are shorter, clearer
  private lazy val renaming: immutable.Map[Identifier, String] = {
    val varMap = mutable.Map[Identifier, String]()
    // Add variables from the store
    for ((lVar, (term, _)) <- obl.s.g.values) {
      term match {
        case terms.Var(id, _, _) =>
          if (!(varMap contains id)) {
            varMap += id -> safeString(lVar.toString)
           // add if non-existent
          } else if (matches(lVar, id)) {
            varMap(id) = safeString(lVar.toString) // update if better match found
          }
        case _ => ()
      }
    }

    // Add other free variables not in the store
    val fvs = freeVars.map(v => v.id) -- varMap.keys
    val newVars = fvs.map(id => id.name.replaceFirst("@", "_").split('@')(0))
    varMap ++= fvs.zip(newVars)
    varMap.toMap
  }

  private def translateDebugExp(de: DebugExp, prefix: String = "", suffix: String = ""): Unit = {
    de.category match {
      case LoopInvariant() =>
        strings += "  (* Begin loop invariant *)"
        for (child <- de.children) {
          translateDebugExp(child)
        }
        strings += "  (* End loop invariant *)"
      case _: SnapshotShape => // Do nothing
      case _ =>
        de match {
          case ide: ImplicationDebugExp =>
            if (ide.term.isDefined) {
              val filtered = filterPure(ide.term.get)
              if (filtered.isDefined) {
                val LHS = translateTerm(filtered.get)
                ide.children.foreach { translateDebugExp(_, prefix + s"$LHS \\<longrightarrow> (", ")" + suffix) }
              }
            }
          case qde: QuantifiedDebugExp =>
            val qvarString = ""
            qde.children.foreach { translateDebugExp(_, prefix + qvarString, suffix) }
          case _ =>
            if (!de.isInternal_) {
              if (de.finalExp.isDefined && notPermExp(de.finalExp.get)) {
                strings += s"  assumes ${de.id}: \"$prefix${translateExp(de.finalExp.get)}$suffix\""
              } else if (de.term.isDefined) {
                if (notSnap(de.term.get)) {
                  val filtered = filterPure(de.term.get)
                  if (filtered.isDefined)
                    strings += s"  assumes ${de.id}: \"$prefix${translateTerm(filtered.get)}$suffix\""
                }
              }
            }
        }
    }
  }
}

// Things that will never be dependent on the particular program
object ExportUtils {
  val FN_ARR = "\\<Rightarrow>"
  val META_ARR = "\\<Longrightarrow>"

  def permCondSimp(p: Term): Term = {
    booleanSimp(isPosSimp(collapseITE(p)))
  }

  def permIsPositive(p: Term): Boolean = permCondSimp(p) == terms.True

  def booleanSimp(c: Term): Term = {
    c match {
      case terms.Ite(c, p0, terms.False) => booleanSimp(terms.And(c, p0))
      case terms.Ite(c, terms.False, p0) => booleanSimp(terms.And())
      case terms.Ite(c, p0, terms.True) => booleanSimp(terms.Implies(c, p0))
      case terms.And(ps) => terms.And(ps.map(booleanSimp))
      case _ => c
    }
  }

  // Silicon permissions are largely of the form (c ? p : Z)
  // If these are nested we collapse them to simplify
  private def collapseITE(p: Term): Term = {
    p match {
      case terms.Ite(c0, terms.Ite(c1, p1, terms.NoPerm), terms.NoPerm) =>
        collapseITE(terms.Ite(terms.And(c0, c1), p1, terms.NoPerm))
      case terms.Ite(c, p0, p1) => terms.Ite(c, collapseITE(p0), collapseITE(p1))
      case terms.PermMinus(p0, p1) => terms.PermMinus(collapseITE(p0), collapseITE(p1))
      case terms.PermMin(p0, p1) => terms.PermMin(collapseITE(p0), collapseITE(p1))
      case _ => p
    }
  }

  // Takes a permission amount p and simplifies it to a boolean term describing when p > 0
  private def isPosSimp(p: Term): Term = {
    p match {
      case terms.FullPerm => terms.True
      case terms.NoPerm => terms.False
      case terms.FractionPermLiteral(r) => if (r > Rational.zero) terms.True else terms.False
      case terms.PermMinus(terms.FullPerm, terms.NoPerm) => terms.True
      case terms.PermMinus(terms.NoPerm, terms.FullPerm) => terms.False
      case terms.PermMinus(terms.FullPerm, p0) => notFullSimp(p0)
      case terms.PermMinus(p0, terms.Ite(c, p1, p2)) =>
        isPosSimp(terms.Ite(c, terms.PermMinus(p0, p1), terms.PermMinus(p0, p2)))
      case terms.PermMin(p0, terms.FullPerm) => isPosSimp(p0)
      case terms.PermMin(terms.Ite(c, p0, p1), p2) =>
        isPosSimp(terms.Ite(c, terms.PermMin(p0, p2), terms.PermMin(p1, p2)))
      case terms.PermMin(p0, terms.Ite(c, p1, p2)) =>
        isPosSimp(terms.Ite(c, terms.PermMin(p0, p1), terms.PermMin(p0, p2)))
      case terms.PermMin(p0, p1) => terms.And(isPosSimp(p0), isPosSimp(p1))
      case terms.Ite(c, terms.FullPerm, terms.NoPerm) => c
      case terms.Ite(c, terms.NoPerm, terms.FullPerm) => terms.Not(c)
      case terms.Ite(p0, p1, terms.FullPerm) => terms.Implies(p0, isPosSimp(p1))
      case terms.Ite(p0, p1, terms.NoPerm) => terms.And(p0, isPosSimp(p1))
      case terms.Ite(p0, p1, p2) => terms.Ite(p0, isPosSimp(p1), isPosSimp(p2))
      case _ => booleanSimp(terms.PermLess(terms.NoPerm, p))
    }
  }

  // Counterpoint to the above, describing when p < 1
  private def notFullSimp(p: Term): Term = {
    p match {
      case terms.FullPerm => terms.False
      case terms.NoPerm => terms.True
      case terms.FractionPermLiteral(r) => if (r < Rational.one) terms.True else terms.False
      case terms.PermMinus(terms.FullPerm, terms.NoPerm) => terms.False
      case terms.PermMinus(terms.FullPerm, p1) => notFullSimp(p1)
      case terms.PermMinus(p0, terms.Ite(c, p1, p2)) =>
        notFullSimp(terms.Ite(c, terms.PermMinus(p0, p1), terms.PermMinus(p0, p2)))
      case terms.PermMin(p0, terms.FullPerm) => notFullSimp(p0)
      case terms.PermMin(terms.FullPerm, p1) => notFullSimp(p1)
      case terms.PermMin(p0, p1) => terms.Or(notFullSimp(p0), notFullSimp(p1))
      case terms.Ite(p0, terms.FullPerm, terms.NoPerm) => terms.Not(p0)
      case terms.Ite(p0, terms.NoPerm, terms.FullPerm) => p0
      case terms.Ite(p0, p1, terms.FullPerm) => terms.And(p0, notFullSimp(p1))
      case terms.Ite(p0, p1, terms.NoPerm) => terms.Implies(p0, notFullSimp(p1))
      case terms.Ite(p0, p1, p2) => terms.Ite(p0, notFullSimp(p1), notFullSimp(p2))
      case _ => terms.PermLess(p, terms.FullPerm)
    }
  }

  def permCondSimpExp(e: Exp): Exp = {
    assert(e.typ == ast.Perm, s"permCondSimpExp expects a perm type but recieved ${e.typ}")
    Simplifier.simplify(posExpCond(collapseCondExp(e)))
  }

  def permIsPositive(e: Exp): Boolean = {
    posExpCond(e) match {
      case _: ast.TrueLit => true
    }
  }

  def booleanExpSimp(c: Term): Term = {
    c match {
      case terms.Ite(c, p0, terms.False) => booleanSimp(terms.And(c, p0))
      case terms.Ite(c, terms.False, p0) => booleanSimp(terms.And())
      case terms.Ite(c, p0, terms.True) => booleanSimp(terms.Implies(c, p0))
      case terms.And(ps) => terms.And(ps.map(booleanSimp))
      case _ => c
    }
  }

  // Silicon permissions are largely of the form (c ? p : Z)
  // If these are nested we collapse them to simplify
  private def collapseCondExp(p: Exp): Exp = {
    p match {
      case ast.CondExp(c0, ast.CondExp(c1, p1, ast.NoPerm()), ast.NoPerm()) =>
        collapseCondExp(ast.CondExp(ast.And(c0, c1)(), p1, ast.NoPerm()())())
      case ast.CondExp(c, p0, p1) => ast.CondExp(c, collapseCondExp(p0), collapseCondExp(p1))()
      case ast.PermSub(p0, p1) => ast.PermSub(collapseCondExp(p0), collapseCondExp(p1))()
      case ast.DebugPermMin(p0, p1) => ast.DebugPermMin(collapseCondExp(p0), collapseCondExp(p1))()
      case _ => p
    }
  }

  // Takes a permission amount p and simplifies it to a boolean term describing when p > 0
  private def posExpCond(p: Exp): Exp = {
    p match {
      case _: ast.FullPerm => ast.TrueLit()()
      case _: ast.NoPerm => ast.FalseLit()()
      case ast.FractionalPerm(num, _) => num match {
        case ast.IntLit(i) => if (i == BigInt(0)) ast.FalseLit()() else ast.TrueLit()()
        case _ => ast.FalseLit()()
      }
      case ast.PermSub(ast.NoPerm(), _) => ast.FalseLit()()
      case ast.PermSub(ast.FullPerm(), ast.FullPerm()) => ast.FalseLit()()
      case ast.PermSub(ast.FullPerm(), ast.NoPerm()) => ast.TrueLit()()
      case ast.PermSub(ast.FullPerm(), p1) => notFullExpCond(p1)
      case ast.PermSub(p0, p1) => ast.PermLtCmp(p0, p1)()

      case ast.DebugPermMin(p0, ast.FullPerm()) => posExpCond(p0)
      case ast.DebugPermMin(p0, p1) => ast.And(posExpCond(p0), posExpCond(p1))()
      case ast.CondExp(c, ast.FullPerm(), ast.NoPerm()) => c
      case ast.CondExp(c, ast.NoPerm(), ast.FullPerm()) => ast.Not(c)()
      case ast.CondExp(p0, p1, ast.FullPerm()) => ast.Implies(p0, posExpCond(p1))()
      case ast.CondExp(p0, p1, ast.NoPerm()) => ast.And(p0, posExpCond(p1))()
      case ast.CondExp(p0, p1, p2) => ast.CondExp(p0, posExpCond(p1), posExpCond(p2))()
      case _ => Simplifier.simplify(ast.PermLtCmp(ast.NoPerm()(), p)())
    }
  }

  // Counterpoint to the above, describing when p < 1
  private def notFullExpCond(p: Exp): Exp = {
    p match {
      case ast.FullPerm() => ast.FalseLit()()
      case ast.NoPerm() => ast.TrueLit()()
      case ast.FractionalPerm(num, den) =>
        (num, den) match {
          case (ast.IntLit(x), ast.IntLit(y)) => if (x == y) ast.FalseLit()() else ast.TrueLit()()
          case _ => ast.FalseLit()()
        }
      case ast.PermSub(ast.FullPerm(), ast.NoPerm()) => ast.FalseLit()()
      case ast.PermSub(ast.NoPerm(), _) => ast.TrueLit()()
      case ast.PermSub(ast.FullPerm(), p1) => notFullExpCond(p1)
      case ast.PermSub(p0, ast.FullPerm()) => notFullExpCond(p0)
      case ast.DebugPermMin(ast.FullPerm(), p1) => notFullExpCond(p1)
      case ast.DebugPermMin(p0, p1) => ast.Or(notFullExpCond(p0), notFullExpCond(p1))()
      case ast.CondExp(p0, ast.FullPerm(), ast.NoPerm()) => ast.Not(p0)()
      case ast.CondExp(p0, ast.NoPerm(), ast.FullPerm()) => p0
      case ast.CondExp(p0, p1, ast.FullPerm()) => ast.And(p0, notFullExpCond(p1))()
      case ast.CondExp(p0, p1, ast.NoPerm()) => ast.Implies(p0, notFullExpCond(p1))()
      case ast.CondExp(p0, p1, p2) => ast.CondExp(p0, notFullExpCond(p1), notFullExpCond(p2))()
      case _ => ast.PermLtCmp(p, ast.FullPerm()())()
    }
  }

  val varVersionRegex = """([^@]+)@(\d+)@(\d+)""".r
  def nameHead(name: String): String = name.split('@')(0)
  def idHead(id: Identifier): String = nameHead(id.name)
  def nameWithoutVersion(name: String) = name.substring(0, name.lastIndexOf("@"))

  // Removes special Isabelle chars
  def safeId(id: Identifier): String = {
    val triVar = """([^@]+)@(\d+)@(\d+)""".r
    id.name match {
      case triVar(a, b, _) => safeString(s"${a}_$b")
      case _ => safeString(id.name)
    }
  }

  // Removes special Isabelle chars
  def safeString(name: String): String = {
    var safe = name.replace('@', '_').filterNot(_ == '$')
    if (safe.contains("%precondition")) {
      safe = safe.takeWhile(_ != '%') + "_pre"
    }
    if (safe.contains("%limited")) {
      safe = safe.takeWhile(_ != '%')
    }
    safe.split('[')(0)
  }

  def padString(s: String, n: Int): String = {
    s + (" " * (n - s.length))
  }

  def matches(lVar: ast.AbstractLocalVar, id: Identifier): Boolean = {
    idHead(id) == lVar.name
  }

  def notSnap(term: Term): Boolean = {
    term match {
      case terms.BuiltinEquals(_, snap) => snap.sort != terms.sorts.Snap
      case _ => true
    }
  }

  def notPermExp(e: Exp): Boolean = {
    e match {
      case _: PermExp
           | _: ast.PermLeCmp
           | _: ast.PermLtCmp
           | _: ast.PermGeCmp
           | _: ast.PermGtCmp => false
      case ast.Forall(_, _, body) => notPermExp(body)
      case _ => true
    }
  }

  def quantifierToString(q: terms.Quantifier): String = {
    q match {
      case terms.Forall => "\\<forall>"
      case terms.Exists => "\\<exists>"
    }
  }

  def translateType(t: ast.Type): String = {
    t match {
      case ast.Int => "int"
      case ast.Bool => "bool"
      case ast.Perm => "perm" // TODO: maybe remove? Or make unit/error
      case ast.Ref => "ref"
      case ast.SeqType(elem) => translateType(elem) + " list"
      case ast.SetType(elem) => translateType(elem) + " fset"
      case ast.MultisetType(elementType) => translateType(elementType) + " multiset"
      case ast.MapType(keyType, valueType) => s"(${translateType(keyType)}, ${translateType(valueType)}) fmap"
      case ast.DomainType(name, vars) => name
      case ast.TypeVar(name) => "'" + name.toLowerCase()
      case _ => "other_type"
    }
  }

  def translateSort(sort: Sort): String = {
    sort match {
      case sorts.Snap => "error: Snap sort"
      case sorts.Int => "int"
      case sorts.Bool => "bool"
      case sorts.Ref => "ref"
      case sorts.Perm => "perm"
      case sorts.Unit => "unit"
      case sorts.Seq(elementsSort) => translateSort(elementsSort) + " list"
      case sorts.Set(elementsSort) => translateSort(elementsSort) + " fset"
      case sorts.Multiset(elementsSort) => translateSort(elementsSort) + " multiset"
      case sorts.Map(keySort, valueSort) => s"(${translateSort(keySort)}, ${translateSort(valueSort)}) fmap"
      case sorts.UserSort(id) => safeString(id.name)
      case sorts.SMTSort(id) => safeString(id.name)
      case sorts.FieldValueFunction(codomainSort, _) => "" // TODO
      case sorts.PredicateSnapFunction(codomainSort, _) => "" // TODO
      case sorts.MagicWandSnapFunction => "" // TODO
      case sorts.FieldPermFunction() => "" // TODO
      case sorts.PredicatePermFunction() => "" // TODO
    }
  }

  def validName(name: String): Boolean = {
    val isabelleKeywords = Seq("value")
    !isabelleKeywords.contains(name)
  }

  private def containsPrecondition(e: Exp, p: Program): Boolean = {
    e match {
      case ast.FuncApp(funcname, args) =>
        val thisFunHasPres = p.findFunctionOptionally(funcname) match {
          case None => false
          case Some(fn) => fn.pres.nonEmpty
        }
        val argsHavePres = args.exists(containsPrecondition(_, p))
        thisFunHasPres || argsHavePres
      case _ => e.subExps.exists(containsPrecondition(_, p))
    }
  }

  def getPrecPropagationExp(fn: ast.Function, p: Program): Option[Exp] = {
    fn.body match {
      case None => None
      case Some(body) =>
        if (fn.pres.isEmpty) {
          val argsExps = fn.formalArgs.map(a =>
            ast.LocalVar(a.name, a.typ)(a.pos, a.info, a.errT)
          )
          val fnPre = ast.FuncApp(fn.name+"$precondition", argsExps)(fn.pos, fn.info, ast.Bool, fn.errT)
          Some(ast.Implies(fnPre, preconditionPropagationExp(body, p))())
        } else {
          Some(preconditionPropagationExp(body, p))
        }
    }
  }

  // Expects the expression to be a variable
  def varToVar(v: ast.LocalVarDecl): ast.LocalVar = {
    ast.LocalVar(v.name, v.typ)()
  }

  /** Follows the same logic as silver.FunctionPreconditionTransformer.transform
    *
    * This expects to only be called on function bodies, and so e should be pure.
    * It also only returns the body of the axiom, it might need to be guarded by the
    * precondition of the function itself.
    */
  def preconditionPropagationExp(e: Exp, p: Program): Exp = {
    def rec(e2: Exp): Exp = preconditionPropagationExp(e2, p)

    e match {
      case e: ast.Literal => ast.TrueLit()(e.pos, e.info, e.errT)
      case ast.And(left, right) =>
        val rhs = ast.Implies(left, rec(right))(right.pos, right.info, right.errT)
        ast.And(rec(left), rhs)(e.pos, e.info, e.errT)
      case ast.Or(left, right) =>
        val rhs = ast.Implies(ast.Not(left)(right.pos, right.info, right.errT), rec(right))(right.pos, right.info, right.errT)
        ast.And(rec(left), rhs)(e.pos, e.info, e.errT)
      case ast.Implies(left, right) =>
        val rhs = ast.Implies(left, rec(right))(right.pos, right.info, right.errT)
        ast.And(rec(left), rhs)(e.pos, e.info, e.errT)
      case ast.CondExp(cond, thn, els) =>
        val cond2 = ast.CondExp(cond, rec(thn), rec(els))(e.pos, e.info, e.errT)
        ast.And(rec(cond), cond2)(e.pos, e.info, e.errT)
      case ast.Let(variable, exp, body) =>
        val body2 = ast.Let(variable, exp, rec(body))(e.pos, e.info, e.errT)
        ast.And(rec(exp), body2)(e.pos, e.info, e.errT)
      case ast.Forall(variables, triggers, body) =>
        val body2 = rec(body)
        body2 match {
          case _: ast.TrueLit => body2
          case _ => ast.Forall(variables, triggers, exp = body2)(e.pos, e.info, e.errT)
        }
      case ast.Exists(variables, triggers, body) =>
        val body2 = rec(body)
        body2 match {
          case _: ast.TrueLit => body2
          case _ => ast.Exists(variables, triggers, exp = body2)(e.pos, e.info, e.errT)
        }

      case ast.FuncApp(funcname, args) =>
        val args2 = bigAnd(args.map(rec), e.pos, e.info, e.errT)
        val fnOpt = p.findFunctionOptionally(funcname)
        if (fnOpt.isDefined && fnOpt.get.pres.isEmpty) {
          args2
        } else {
          val fnPre = ast.FuncApp(funcname + "%precondition", args)(e.pos, e.info, ast.Bool, e.errT)
          ast.And(fnPre, args2)(e.pos, e.info, e.errT)
        }
      case other => bigAnd(other.subExps.map(rec), other.pos, other.info, other.errT)
    }
  }

  // Note, will remove Trues
  private def bigAnd(es: Seq[Exp], pos: ast.Position, info: ast.Info, errT: ast.ErrorTrafo): Exp = {
    val filtered = es.collect{ case e: ast.TrueLit => e }
    if (filtered.isEmpty) ast.TrueLit()(pos, info, errT)
    else if (filtered.length == 1) es.head
    else {
      ast.And(filtered.head, bigAnd(filtered.tail, pos, info, errT))(pos, info, errT)
    }
  }

  sealed trait MemberName {
    val name: String
  }
  case class DomainName(name: String) extends MemberName
  case class FunctionName(name: String) extends MemberName
  case class PredicateName(name: String) extends MemberName
  type MemberSeq = Seq[MemberName]

  def localeName(m: MemberSeq): String = m.head.name + "_" + m.tail.map(_.name).mkString("_")

  // Dependency graph between functions, domains and predicates
  def getDependencyGraph(program: Program): DefaultDirectedGraph[MemberName, DefaultEdge] = {
    val graph = new DefaultDirectedGraph[MemberName, DefaultEdge](classOf[DefaultEdge])
    val domains = program.domains.filter(d => !d.name.endsWith("WellFoundedOrder"))

    domains.foreach(d => graph.addVertex(DomainName(d.name)))
    program.functions.foreach(f => graph.addVertex(FunctionName(f.name)))
    program.predicates.foreach(p => graph.addVertex(PredicateName(p.name)))

    def process(caller: MemberName, e: Exp): Unit = {
      e visit {
        case df: ast.DomainFuncApp => graph.addEdge(caller, DomainName(df.domainName))
        case ast.FuncApp(funcname, _) => graph.addEdge(caller, FunctionName(funcname))
        case ast.PredicateAccessPredicate(loc, _) => graph.addEdge(caller, PredicateName(loc.predicateName))
      }
    }

    for (d <- domains) {
      d.axioms.foreach(ax => process(DomainName(d.name), ax.exp))
    }
    for (f <- program.functions) {
      allSubexpressions(f).foreach(process(FunctionName(f.name), _))
    }
    for (p <- program.predicates) {
      p.body.foreach(process(PredicateName(p.name), _))
    }

    graph
  }

  // Returns ordered list of MemberSeq and any other MemberSeqs it depends on
  // Based on Functions.heights and DefaultFunctionVerificationUnitProvider.analyze
  // This could use the chopper to slice a relevant subprogram
  def memberTranslationSequence(program: Program): Seq[(MemberSeq, Seq[MemberSeq])] = {
    // This could use the position of each member to create a unified ordering,
    // Map[MemberName, Position]
    val functionIndices = program.functions.map(_.name).zipWithIndex.toMap
    val domainIndices = program.domains.filter(d => !d.name.endsWith("WellFoundedOrder")).map(_.name).zipWithIndex.toMap
    val predicateIndices = program.predicates.map(_.name).zipWithIndex.toMap

    implicit val memberNameOrdering: Ordering[MemberName] =
      Ordering.by[MemberName, (Int, Int)] {
        case DomainName(name) => (0, domainIndices(name))
        case PredicateName(name) => (1, predicateIndices(name))
        case FunctionName(name) => (2, functionIndices(name))
      }

    implicit val memberNameSetOrdering: Ordering[MSet[MemberName]] =
      Ordering.by[MSet[MemberName], (Int, MemberName)] {
        s => (s.toList.length, s.toList.min)
      }

    val depGraph = getDependencyGraph(program)
    val stronglyConnectedSets = new GabowStrongConnectivityInspector(depGraph).stronglyConnectedSets().asScala
    val condensedCallGraph = new DefaultDirectedGraph[MSet[MemberName], DefaultEdge](classOf[DefaultEdge])
    stronglyConnectedSets.foreach(v => condensedCallGraph.addVertex(v.asScala))

    def condensationOf(func: MemberName): MSet[MemberName] =
      stronglyConnectedSets.find(_ contains func).get.asScala

    for (e <- depGraph.edgeSet().asScala) {
      val sourceSet = condensationOf(depGraph.getEdgeSource(e))
      val targetSet = condensationOf(depGraph.getEdgeTarget(e))

      if (sourceSet != targetSet)
        condensedCallGraph.addEdge(sourceSet, targetSet)
    }

    assert(!new CycleDetector(condensedCallGraph).detectCycles(),
      "Expected acyclic graph, but found at least one cycle")

    val result = mutable.Buffer[(MemberSeq, Seq[MemberSeq])]()
    for (condensation <- new TopologicalOrderIterator(condensedCallGraph, memberNameSetOrdering).asScala) {
      val deps = condensedCallGraph.outgoingEdgesOf(condensation).asScala.toList.map(
        condensedCallGraph.getEdgeTarget(_).toList.sorted)
      result.prepend((condensation.toList.sorted, deps))
    }
    result.toList
  }
}
