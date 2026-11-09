package viper.silicon.debugger

import org.jgrapht.alg.connectivity.GabowStrongConnectivityInspector
import org.jgrapht.alg.cycle.CycleDetector
import org.jgrapht.graph.{DefaultDirectedGraph, DefaultEdge}
import org.jgrapht.traverse.TopologicalOrderIterator
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.debugger.ExportUtils._
import viper.silicon.debugger.debugger.AnyDebugNode
import viper.silicon.interfaces.state.Chunk
import viper.silicon.{Map, resources}
import viper.silicon.resources.{FieldID, PredicateID}
import viper.silicon.state.State.{DebugOldHeaps, HeapLabel, TemporaryRecord}
import viper.silicon.state._
import viper.silicon.state.terms.sorts.FieldValueFunction
import viper.silicon.state.terms.{Sort, Term, sorts}
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.ast.utility.Functions.allSubexpressions
import viper.silver.ast.utility.Simplifier
import viper.silver.ast.{Exp, LocalVar, PermExp, PermGeCmp, PermGtCmp, PermLeCmp, PermLtCmp, Program}
import viper.silver.utility.Common.Rational

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Paths}
import scala.collection.mutable.{ArrayBuffer, Set => MSet}
import scala.collection.{immutable, mutable}
import scala.io.StdIn.readLine
import scala.jdk.CollectionConverters._


// Main wrapper object
object DebugExporter {
  def exportIsabelle(obl: ProofObligation): Unit = {

    val exp = obl.eAssertion.finalExp.get
    println(s"Isabelle assertion: $exp at ${exp.pos}" )

    println(s"Enter a file name:")
    val userInput = readLine()
    if (userInput.equals("q") || userInput.equals("Q")) return
    if (userInput.isEmpty) {
      println("No filename entered, export skipped.")
      return
    }

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

      val filename = filepath.getFileName.toString.split('.')(0)
      val t = new Translator(obl, filename)
      t.translateObligation()

      // Write to file
      val writer = Files.newBufferedWriter(filepath, StandardCharsets.UTF_8)
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

/**
  * Generates an Isabelle lemma, corresponding to the proof obligation.
  * The result is stored in `strings`, filename is only used to title the theory.
  */
class Translator(val obl: ProofObligation, val filename: String) {
  private val state = obl.s
  private val program = obl.s.program
  private val store = obl.s.g
  private val domains = program.domains.filter(d => !d.name.endsWith("WellFoundedOrder"))
  private val membersInTranslationOrder: Seq[(MemberSeq, Seq[MemberSeq])] = memberTranslationSequence(program)

  var strings = ArrayBuffer[String]() // Strings to be written to .thy file
  // Used to remove duplicates. After renaming/replacement some PCs might collide.
  private val printedAssumptions = mutable.Set[String]()

  // Maps each debug heap label to its dominant heap label
  private val heapLabelMap: Map[String, String] =
    ExportUtils.heapLabelMap(state.debugOldHeaps, state.temporaryHeapRecord)
  private val currentHeapLabel: String = obl.v.getDebugHeapLabel(obl.s).getOrElse("currentHeapMissing")
  private val currentDomHeapLabel: String = heapLabelMap.getOrElse(currentHeapLabel, currentHeapLabel)
  private val isabelleCurrentHeap = "h\\<^sub>c"
  private val DebugHeapLabel = "debug@(\\d+)".r

  // Definitions of fresh variables Silicon introduced, keyed by the fresh variable's term.
  // Definitions are only collected from plain groups, not from under implications or quantifiers,
  // since there they would only hold conditionally.
  private val freshVarDefinitions: immutable.Map[Term, FreshVarDefinition] = {
    def collect(node: AnyDebugNode): Iterable[(Term, FreshVarDefinition)] = node match {
      case varDef: FreshVarDefinition => Some(varDef.freshVarTerm -> varDef)
      case group: DebugGroup => group.children.flatMap(collect)
      case invariant: DebugInvariant => invariant.children.flatMap(collect)
      case _ => None
    }
    obl.assumptionsExp.toSeq.flatMap(collect).toMap
  }

  private def isFreshVar(term: Term): Boolean =
    freshVarDefinitions.contains(term)

  // Maps SSA versions of local variables to a current store variable
  // If x -> x_2; y -> y_3, z -> y_3
  // Then result maps x_2 -> x; y_3 -> y
  private val storeRenames: immutable.Map[String, String] = {
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
        case _ =>
      }
    }
    varRenames.toMap
  }

  // Debug heaps in the order they were created. debugOldHeaps is a Map, so its iteration order says
  // nothing, but "debug@N" labels are numbered in creation order. Other labels ("old", user labels)
  // name heaps that are also recorded under a "debug@N" label, so they come last.
  private val heapsInCreationOrder: Seq[(HeapLabel, HeapRecord)] = {
    val (debugHeaps, labelledHeaps) = state.debugOldHeaps.toSeq.partition(h => DebugHeapLabel.matches(h._1))
    debugHeaps.sortBy { case (DebugHeapLabel(n), _) => n.toInt } ++ labelledHeaps.sortBy(_._1)
  }

  /** `fieldVarDefinitions` maps terms that are fresh variable definitions to their first heap occurrence.
    * When printing, these terms should all be replaced by this field chunk.
    * `predicateChunks` maps predicate snapshots to their first heap occurrence.
    * `qfcSnapMapRenamings` maps snapshot maps to their first heap occurrence, and a renaming of the snapshot map that
    *   includes the field name. This does not record singleton QFCs.
    * `quantPredChunks` maps predicate snapshot maps to their first heap occurrence. Currently not used.
    * `usedVarDefinitions` notes fresh variable definitions that do not need to be printed again as a PC
    */
  private val (fieldVarDefinitions: immutable.Map[Term, (BasicChunk, HeapLabel)],
               predicateChunks: immutable.Map[Term, (BasicChunk, HeapLabel)],
               qfcSnapMapRenamings: immutable.Map[Term, (QuantifiedFieldChunk, String)],
               singletonQFCs: immutable.Map[Term, (QuantifiedFieldChunk, HeapLabel)],
               quantPredChunks: immutable.Map[Term, (QuantifiedPredicateChunk, String)],
               usedVarDefinitions: immutable.Set[FreshVarDefinition]) = {
    val fields = mutable.Map[Term, (BasicChunk, HeapLabel)]()
    val predicates = mutable.Map[Term, (BasicChunk, HeapLabel)]()
    val quantFields = mutable.Map[Term, (QuantifiedFieldChunk, String)]()
    val qfcCounter: mutable.Map[String, Int] = mutable.Map(program.fields.map(_.name).map((_, 0)): _*)
    val singletons = mutable.Map[Term, (QuantifiedFieldChunk, HeapLabel)]()
    val quantPredicates = mutable.Map[Term, (QuantifiedPredicateChunk, HeapLabel)]()
    val usedDefs = mutable.Set[FreshVarDefinition]()

    for ((label, record) <- heapsInCreationOrder) {
      for (chunk <- record.heap.values) {
        chunk match {
          case bfc: BasicChunk if bfc.resourceID == FieldID =>
            // If the chunk's term is a fresh variable, add it to the replacements
            if ((isFreshVar(bfc.snap)) && !(fields contains bfc.snap) && permIsPositive(bfc.perm)) {
              fields += bfc.snap -> (bfc, label)
              usedDefs += freshVarDefinitions(bfc.snap)
            }
          case bpc: BasicChunk if bpc.resourceID == PredicateID =>
            if (!(predicates contains bpc.snap) && permIsPositive(bpc.perm))
              predicates += bpc.snap -> (bpc, label)
          case qfc: QuantifiedFieldChunk if qfc.singletonRcvr.isEmpty =>
            if (!(quantFields contains qfc.snapshotMap)) {
              val field = qfc.id.name
              val mapLabel = s"${field}Map${qfcCounter(field)}"
              qfcCounter(field) = qfcCounter(field) + 1
              quantFields += (qfc.snapshotMap -> (qfc, mapLabel))
            }
          case qfc: QuantifiedFieldChunk if qfc.singletonRcvr.isDefined =>
            if (!(singletons contains qfc.singletonRcvr.get)) {
              // TODO: I don't check permission yet, not sure if we have to
              singletons += qfc.snapshotMap -> (qfc, label)
            }
          case qpc: QuantifiedPredicateChunk =>
            quantPredicates += (qpc.snapshotMap -> (qpc, label))
          case _ =>
        }
      }
    }
    (fields.toMap, predicates.toMap, quantFields.toMap, singletons.toMap, quantPredicates.toMap, usedDefs.toSet)
  }

  private val fieldReplacementsByName: immutable.Map[String, (BasicChunk, String)] =
    fieldVarDefinitions.collect { case (terms.Var(id, _, _), loc) => nameWithoutVersion(id.name) -> loc }

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
        val nameString = padString(fld.name, fieldLength)
        val notation = s"(\"_:_\\<cdot>${fld.name}\" [1000, 1000] 999)"
        strings += s"  fixes $nameString :: \"Heap $FN_ARR ref $FN_ARR ${translateType(fld.typ)}\" $notation"
      }
      strings += "\n"
    }
  }

  // Field lookup using the notation declared in defineFields: `heap:ref\<cdot>field`.
  // Heap and ref must be atomic (priority 1000), so callers should translate the ref with parenthesisLevel 100.
  private def fieldAccess(field: String, heap: String, ref: String): String =
    s"$heap:$ref\\<cdot>$field"

  // Predicate notation declared in declarePredicate: `heap:P(arg1, ..., argN)`, e.g. "_:list'(_,/ _')".
  // The heap is atomic (priority 1000); the arguments are enclosed by the parentheses, so they can be any term.
  private def predicateNotation(pred: ast.Predicate): String = {
    val argSlots = pred.formalArgs.map(_ => "_").mkString(",/ ")
    val priorities = (1000 +: pred.formalArgs.map(_ => 0)).mkString(", ")
    s"(\"_:${pred.name}'($argSlots')\" [$priorities] 999)"
  }

  // Predicate instance using the notation declared in declarePredicate: `heap:P(arg1, ..., argN)`.
  // The heap must be atomic; the args need no parentheses.
  private def predicateAccess(pred: String, heap: String, args: Seq[String]): String =
    s"$heap:$pred(${args.mkString(", ")})"

  // P_eq states that two heaps agree on the footprint of the predicate instance P(args).
  // It takes the two heaps, then the arguments as a tuple if there are several: `P_eq h h' (x, y)`.
  // A single argument is passed directly (`P_eq h h' x`), so it must be atomic: translate it with
  // eqArgLevel, which gives parenthesisLevel 100 for one argument and 0 for tuple components.
  private def predicateEq(pred: String, heap1: String, heap2: String, args: Seq[String]): String = args match {
    case Seq() => s"${pred}_eq $heap1 $heap2"
    case Seq(arg) => s"${pred}_eq $heap1 $heap2 $arg"
    case _ => s"${pred}_eq $heap1 $heap2 (${args.mkString(", ")})"
  }

  private def eqArgLevel(numArgs: Int): Int = if (numArgs == 1) 100 else 0

  private def predicateEqType(pred: ast.Predicate): String = {
    val argTypes = pred.formalArgs.map(a => translateType(a.typ))
    val argType = argTypes match {
      case Seq() => ""
      case Seq(t) => s"$t $FN_ARR "
      case _ => s"${argTypes.mkString(" \\<times> ")} $FN_ARR "
    }
    s"Heap $FN_ARR Heap $FN_ARR ${argType}bool"
  }

  // Debug labels "debug@N" are written as h_N. Named labels are kept as is.
  // The current heap (or any label whose dominant heap is the current heap) is written as isabelleCurrentHeap.
  private def printHeapLabel(label: String): String = label match {
    case l if l == currentHeapLabel || l == currentDomHeapLabel => isabelleCurrentHeap
    case DebugHeapLabel(n) => "h" + n.map(d => s"\\<^sub>$d").mkString
    case _ => label
  }

  private def translateMembers(): Unit = {
    strings += "text \\<open>Translate domains, functions and predicates\\<close>\n"

    for ((mSeq, deps) <- membersInTranslationOrder) {
      val depLocales = (if (memberSeqIsHeapDep(mSeq)) "\n  Fields +" else "") +
        deps.map(m => s"\n  ${localeName(m)} +").mkString("")
      strings += s"locale ${localeName(mSeq)} =" + depLocales
      translateMemberSeq(mSeq)
      strings += ""
    }
    strings += ""
  }

  // Whether any member in the sequence is heap dependent
  private def memberSeqIsHeapDep(members: MemberSeq): Boolean = {
    members.exists {
      case DomainName(_) => false
      case FunctionName(name) => !program.findFunction(name).isPure
      case PredicateName(name) => !program.findPredicate(name).body.exists(_.isPure)
    }
  }

  // Translate a single collection of inter-dependent members
  private def translateMemberSeq(members: MemberSeq): Unit = {
    for (member <- members) {
      member match {
        case DomainName(name) => declareDomain(program.findDomain(name))
        case FunctionName(name) => declareFunction(program.findFunction(name))
        case PredicateName(name) => declarePredicate(program.findPredicate(name))
      }
    }
    for (member <- members) {
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
    var argStringWTypes = argStringWithTypes(fn.formalArgs, !fn.isPure)

    // Translate function body
    if (fn.body.isDefined) {
      val fnRHS = translateExp(fn.body.get)
      val preString = if (fn.pres.nonEmpty) s"${fn.name}_pre $argString $META_ARR " else ""
      strings += s"  assumes ${fn.name}_def: \"$preString${fn.name} $argString \\<equiv>\n    $fnRHS\""

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
      val argString2 = "h'" + argString.drop(1)
      val footprint = fn.pres.filter(!_.isPure).map(translateExp(_, parenthesisLevel = 10, isFrameAxiom = true)).mkString(" \\<and> ")
      strings += s"  assumes ${fn.name}_framing: \"" +
        s"${fn.name}_pre $argString \\<and> ${fn.name}_pre $argString2"
      strings += s"    \\<and> $footprint"
      strings += s"    $META_ARR ${fn.name} $argString = ${fn.name} $argString2\""
    }
  }

  private def declarePredicate(pred: ast.Predicate): Unit = {
    val typeString = s"Heap $FN_ARR " + pred.formalArgs.map(a => translateType(a.typ) + s" $FN_ARR ").mkString("")
    strings += s"  fixes ${pred.name} :: \"${typeString}bool\" ${predicateNotation(pred)}"
    strings += s"  fixes ${pred.name}_eq :: \"${predicateEqType(pred)}\""
  }

  private def definePredicate(pred: ast.Predicate): Unit = {
    pred.getPureFragment match {
      case Some(exp) =>
        val predString = predicateAccess(pred.name, "h", pred.formalArgs.map(_.name))
        val bodyString = translateExp(exp, parenthesisLevel = 51)
        strings += s"  assumes unfold_${pred.name}: \"" +
          s"$predString $META_ARR\n    $bodyString\""
      case None =>
    }
    pred.getAccessFragment match {
      case Some(exp) =>
        val eqString = predicateEq(pred.name, "h", "h'", pred.formalArgs.map(_.name))
        val bodyString = translateExp(exp, parenthesisLevel = 51, isFrameAxiom = true)
        strings += s"  assumes ${pred.name}_eq_def: \"$eqString $META_ARR"
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

    val locales = mutable.Buffer[String]()
    if (program.fields.nonEmpty) locales += "  Fields"
    membersInTranslationOrder.foreach { case (mSeq, _) => locales += "  " + localeName(mSeq) }
    if (locales.isEmpty)
      strings += "  assumes True (* no program definitions *)"
    else
      strings += locales.mkString(" +\n") + '\n'

    strings += "\ncontext Program\nbegin\n\nlemma"
    translateStore()
    translateHeaps()
    strings += "  (* Assumptions *)"
    obl.assumptionsExp.toSeq.sortBy(_.id).foreach(translateDebugNode(_))

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
    for ((localVar, term) <- store.termValues) {
      strings += s"  fixes ${localVar.name} :: \"${translateSort(term.sort)}\""
    }
    for ((localVar, (term, _)) <- store.values) {
      term match {
        case _: terms.Literal =>
          val value = translateTerm(term)
          strings += s"  assumes store_${localVar.name}: \"${localVar.name} = $value\""
        case _ => freshVarDefinitions.get(term) match {
          case Some(varDef) =>
            val value = translateExp(varDef.rhsNew)
            strings += s"  assumes store_${localVar.name}: \"${localVar.name} = $value\""
          case None => // No definition to print
        }
      }
    }
  }

  private def translateHeaps(): Unit = {
    // Ignore any heaps (e.g. debug@0) from the precondition that are not "old"
    val heapsExclPreOld = state.debugOldHeaps.filter { case (label, record) =>
      // Remove heaps inhale pre heaps that aren't labelled 'old'
      (record.cause != InhalePre || label == Verifier.PRE_STATE_LABEL) &&
      // Remove heaps generated by checking loop invariants
      record.cause != ExhaleInv }
    for ((label, record) <- heapsExclPreOld) {
      if (label == currentHeapLabel) strings += s"  (* Current heap *)"
      else {
        label match {
          case DebugHeapLabel(n) => strings += s"  (* Heap $n *)"
          case _ => strings += s"  (* Heap $label *)"
        }
      }
      for ((chunk, idx) <- record.heap.values.zipWithIndex) {
        translateChunk(chunk, label, idx)
      }
    }
  }

  // Returns the location of a chunk, e.g. "heap:x.f".
  // NOTE: assumes permission is positive.
  private def basicFieldChunkLocation(chunk: BasicChunk, heapLabel: String): String = {
    assert(chunk.resourceID == FieldID, "basicFieldChunkLocation got the wrong chunk...")
    val ref = chunk.argsExp match {
      // I think it should always have an argsExp ???
      case Some(args) => translateExp(args.head, parenthesisLevel = 100)
      case None => translateTerm(chunk.args.head, parenthesisLevel = 100)
    }
    val domHeapLabel = heapLabelMap.getOrElse(heapLabel, "missing:"+heapLabel)
    fieldAccess(chunk.id.name, printHeapLabel(domHeapLabel), ref)
  }

  private def translateChunk(chunk: Chunk, heapLabel: String, idx: Int): Unit = {
    chunk match {
      case basic: BasicChunk =>
        basic.resourceID match {
          case FieldID => translateBFC(basic, heapLabel, idx)
          case PredicateID => translateBPC(basic, heapLabel, idx)
        }
      case qfc: QuantifiedFieldChunk => translateQFC(qfc, heapLabel, idx)
      case qpc: QuantifiedPredicateChunk => translateQPC(qpc, heapLabel, idx)
    }
  }

  private def translateBFC(chunk: BasicChunk, heapLabel: String, idx: Int): Unit = {
    require(chunk.args.length == 1, "Method translateChunk expected FieldChunk to have exactly one arg.")
    val assumptionName = s"${printHeapLabel(heapLabel)}_$idx"
    val locString = basicFieldChunkLocation(chunk, heapLabelMap(heapLabel)) // TODO: Idk what this is, simplify
    val valueString = freshVarDefinitions.get(chunk.args.head) match {
      case Some(varDef) =>
        translateExp(varDef.rhsNew)
      case None =>
        chunk.snapExp match {
          case Some(exp) => translateExp(exp)
          case None => locString // TODO: I think this means it is the original snap location, is this always true?
        }
    }
    permCondSimp(chunk.perm) match {
      case terms.True =>
        strings += s"  assumes $assumptionName: \"$locString = $valueString\""
      case cond =>
        strings += s"  assumes $assumptionName: \"${translateTerm(cond)} $META_ARR $locString = $valueString\""
    }
  }

  private def translateBPC(chunk: BasicChunk, heapLabel: String, idx: Int): Unit = {
    def predSnapInOtherHeap(s: Term): Boolean = (predicateChunks contains s) && predicateChunks(s)._2 != heapLabel

    val domHeap = printHeapLabel(heapLabelMap(heapLabel))
    val args = chunk.args.map(translateTerm(_))
    val chunkString = predicateAccess(chunk.id.name, domHeap, args)
    val predEq = if (predSnapInOtherHeap(chunk.snap)) {
      val (_, otherLabel) = predicateChunks(chunk.snap)
      val eqArgs = chunk.args.map(translateTerm(_, parenthesisLevel = eqArgLevel(chunk.args.length)))
      s" \\<and> ${predicateEq(chunk.id.name, domHeap, printHeapLabel(otherLabel), eqArgs)}"
    } else ""
    strings += s"  assumes ${printHeapLabel(heapLabel)}_$idx: \"$chunkString$predEq\""
  }

  private def translateQFC(qfc: QuantifiedFieldChunk, heapLabel: String, idx: Int): Unit = {
    val domLabel = heapLabelMap(heapLabel)

    qfc.singletonRcvrExp match {
      case Some(rcvr) =>
        val rcvr2 = Simplifier.simplify(rcvr)
        val perm = Simplifier.simplify(qfc.permValueExp.get.replace(qfc.quantifiedVarExps.get.head.localVar, rcvr2))
        val permCond = permCondSimpExp(perm)
        val permCondString = permCond match {
          case _: ast.TrueLit => ""
          case _ => translateExp(permCond, oldHeapLabel = Some(domLabel)) + " \\<Longrightarrow> "
        }
        val rcvrString = translateExp(rcvr2, parenthesisLevel = 100)
        val default = translateTerm(qfc.fvf)
          /*qfcSnapMapRenamings.get(qfc.fvf) match {
          case Some((_, str)) => str + " " + rcvrString
          case None => translateTerm(qfc.fvf) + " " + rcvrString
        }
           */
        val eqString = s"${fieldAccess(qfc.id.name, printHeapLabel(domLabel), rcvrString)} = $default"
        strings += s"  assumes ${printHeapLabel(heapLabel)}_$idx: \"$permCondString$eqString\""
      case None =>
        val quantifiedVars = qfc.invs.headOption.map(_.qvarExps.getOrElse(Seq())).getOrElse(Seq())
        val newRenamings = quantifiedVars.map(v => (v.name, cleanName(v)))
        val newRenames = storeRenames ++ newRenamings
        val rcvr = (for (inv <- qfc.invs.headOption; exps <- inv.invertibleExps; e <- exps.headOption)
          yield translateExp(e, parenthesisLevel = 100, newRenames)).getOrElse("missingInvExp")
        val varString = argStringWithTypes(quantifiedVars, includeHeap = false)
        val freeRef = safeString(qfc.quantifiedVarExps.get.head.name)
        val condString = translateExp(qfc.conditionExp.get, oldHeapLabel = Some(heapLabel), renames = newRenames) + s" $META_ARR"
        val permCond = permCondSimpExp(qfc.permValueExp.get) match {
          case ast.TrueLit() => ""
          case e => translateExp(e, oldHeapLabel = Some(domLabel), renames = newRenames) + " \\<longrightarrow> "
        }
        val field = fieldAccess(qfc.id.name, printHeapLabel(domLabel), freeRef)
        val default = qfcSnapMapRenamings.get(qfc.fvf) match {
          case Some((_, snapString)) => s"$snapString $freeRef"
          case None => s"${qfc.id}_${translateTerm(qfc.fvf, renames = newRenames)} $freeRef"
        }
        val chunkString = s"\\<And>$varString. $condString\n    let r = $rcvr in $permCond$field = $default"
        strings += s"  assumes ${printHeapLabel(heapLabel)}_$idx: \"$chunkString\""
    }
  }

  private def translateQPC(qpc: QuantifiedPredicateChunk, heapLabel: String, idx: Int): Unit = {
    def predSnapInOtherHeap(s: Term): Boolean = (predicateChunks contains s) && predicateChunks(s)._2 != heapLabel
    val domLabel = heapLabelMap(heapLabel)

    val condString = translateTerm(terms.And(qpc.condition, permCondSimp(qpc.permValue)))
    val argList = qpc.quantifiedVars.map(_.id.name)
    val quantifyString = "\\<And>" + argList.mkString(" ")
    val predString = s"$quantifyString. $condString $META_ARR ${predicateAccess(qpc.id.name, printHeapLabel(domLabel), argList)}"
    strings += s"  assumes ${printHeapLabel(heapLabel)}_${idx}a: \"$predString\""
    if (predSnapInOtherHeap(qpc.snapshotMap)) {
      val (_, otherLabel) = predicateChunks(qpc.snapshotMap)
      val eqString = predicateEq(qpc.id.name, printHeapLabel(domLabel), printHeapLabel(otherLabel), argList)
      strings += s"  assumes ${printHeapLabel(heapLabel)}_${idx}b: \"$condString $META_ARR $eqString\""
    }
  }

  case class TranslationOptions(parenthesisLevel: Int,
                                collapseSnaps: Boolean,
                                annotateIntLits: Boolean) {
    def annotateIntLitsOff(): TranslationOptions = this.copy(annotateIntLits = false)
  }

  private object TranslationOptions {
    def apply(parenthesisLevel: Int,
              collapseSnaps: Boolean,
              annotateIntLits: Boolean): TranslationOptions = new TranslationOptions(parenthesisLevel,
                collapseSnaps,
                annotateIntLits)
  }

  private val defaultOptions = TranslationOptions(parenthesisLevel = 0, collapseSnaps = false, annotateIntLits = true)

  // Main translation function
  private def translateTerm(term: Term,
                            parenthesisLevel: Int = 0,
                            renames: immutable.Map[String, String] = storeRenames,
                            options: TranslationOptions = defaultOptions): String = {
    // Recursive call, for convenience
    def rec(term2: Term, pLevel: Int, ops: TranslationOptions = options): String = translateTerm(term2, pLevel, renames, options)
    def wrap(s: String, pLevel: Int): String = if (pLevel <= parenthesisLevel) s"($s)" else s
    def recOp(left: Term, op: String, right: Term, pLevel: Int): String = {
      wrap(rec(left, pLevel) + s" $op " + rec(right, pLevel), pLevel)
    }

    if (fieldVarDefinitions contains term) {
      val (chunk, heapLabel) = fieldVarDefinitions(term)
      return wrap(basicFieldChunkLocation(chunk, heapLabel), 100)
    } else if (singletonQFCs contains term) {
      val (chunk, heapLabel) = singletonQFCs(term)
      val location = fieldAccess(chunk.id.name, heapLabel, translateExp(chunk.singletonRcvrExp.get))
      return wrap(location, 100)
    }

    term match {
      // Functions and Applications
      case terms.Var(id, _, _) => renames.getOrElse(id.name, safeId(id))
      case terms.Let(bindings, body) =>
        val bindString = bindings.transform((bVar, bTerm) => rec(bVar, 10) + " = " + rec(bTerm, 10)).mkString("; ")
        wrap(s"let $bindString in ${rec(body, 10)}", 10)
      case terms.Null => "Null"
      case terms.Unit => "UNIT"
      case terms.App(applicable, args) =>
        if (applicable.resultSort.isInstanceOf[FieldValueFunction]) {
          // In this case there are no args and the whole term is the snapshot, which returns a function
          qfcSnapMapRenamings(term)._2
        } else {
          // TODO: if it is spurious precondition then remove it
          val og_fn = applicable.id.name.takeWhile(_ != '%')
          obl.s.program.findFunctionOptionally(og_fn) match {
            case None =>
              // E.g. domain functions
              if (args.isEmpty) safeId(applicable.id)
              else wrap(safeId(applicable.id) + args.map(" " + rec(_, 100)).mkString(""), 100)
            case Some(f) =>
              if (applicable.id.name.contains("%precondition") && f.pres.isEmpty) "True"
              else if (f.isPure)
                wrap(s"${safeId(applicable.id)}" + args.tail.map(" " + rec(_, 100)).mkString(""), 100)
              else {
                val heapLabelString = ??? // TODO
                wrap(s"${safeId(applicable.id)} $heapLabelString " + args.tail.map(rec(_, 100)).mkString(" "), 100)
              }
          }
        }
      // Stuff
      case terms.IntLiteral(i) => if (options.annotateIntLits) s"($i::int)" else i.toString()
      case b: terms.BooleanLiteral => b.toString
      case terms.Quantification(q, vars, body, _, _, _, _) =>
        val varRenames = vars.map(v => (v.id.name, v.id.name.takeWhile(_ != '@')))
        val newRenames = renames ++ varRenames
        val varString = varRenames.map(_._2).mkString(" ")
        wrap(s"${quantifierToString(q)}$varString. ${translateTerm(body, 10, newRenames)}", 10)
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
      case terms.Lookup(_, fvf, at) =>
        s"${rec(fvf, 0)} ${rec(at, 100)}"
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
                           renames: immutable.Map[String, String] = storeRenames,
                           isFrameAxiom: Boolean = false,
                           variablePrime: Boolean = false,
                           resultString: Option[String] = None,
                           oldHeapLabel: Option[String] = None): String = {
    def rec(e2: Exp, pLevel: Int): String = translateExp(e2, pLevel, renames, isFrameAxiom, variablePrime, resultString, oldHeapLabel)
    def wrap(s: String, pLevel: Int): String = if (pLevel <= parenthesisLevel) s"($s)" else s
    def recOp(left: Exp, op: String, right: Exp, pLevel: Int): String = {
      wrap(rec(left, pLevel) + s" $op " + rec(right, pLevel), pLevel)
    }
    val domOldHeapLabel = oldHeapLabel match {
      case Some(label) => printHeapLabel(heapLabelMap(label.takeWhile(_ != '#')))
      case _ => "h"
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
      case ast.And(left, right) if isFrameAxiom && left.isPure => rec(right, parenthesisLevel)
      case ast.And(left, right) if isFrameAxiom && right.isPure => rec(left, parenthesisLevel)
      case ast.And(left, right) =>
        val lPLevel = if (left.isInstanceOf[ast.And]) 34 else 35
        val rPLevel = if (right.isInstanceOf[ast.And]) 34 else 35
        wrap(rec(left, lPLevel) + " \\<and> " + rec(right, rPLevel), 35)
      case ast.Implies(left, right) =>
        val translation = translateExp(left, 25, renames, isFrameAxiom = false, variablePrime, resultString, oldHeapLabel) +
          " \\<longrightarrow> " + rec(right, 25)
        wrap(translation, 25)
      case ast.MagicWand(left, right) => rec(left, 50) + " \\<longrightarrow> " + rec(right, 50) // TODO: remove?
      case ast.Not(exp) =>
        exp match {
          case ast.EqCmp(left, right) => recOp(left, "\\<noteq>", right, 50)
          case ast.SeqContains(elem, s) => recOp(elem, "\\<notin>:", s, 51)
          case ast.AnySetContains(elem, s) =>
            // TODO: fix for multisets?? Also below
            recOp(elem, setOrMSetOp("\\<in>", s.typ), s, 51)
          case _ => wrap("\\<not>" + wrap(rec(exp, 40), 40), 40)
        }
      case ast.TrueLit() => "True"
      case ast.FalseLit() => "False"
      case ast.NullLit() => "Null"
      case ast.FieldAccessPredicate(loc, _) =>
        if (isFrameAxiom) {
          val loc1 = rec(loc.rcv, 100)
          val loc2 = translateExp(loc.rcv, 100, renames, isFrameAxiom, variablePrime = true, resultString)
          s"${fieldAccess(loc.field.name, "h", loc1)} = ${fieldAccess(loc.field.name, "h'", loc2)}"
        }
        else "undefined"
      case ast.PredicateAccessPredicate(loc, _) =>
        if (isFrameAxiom){
          wrap(predicateEq(loc.predicateName, "h", "h'", loc.args.map(rec(_, eqArgLevel(loc.args.length)))), 100)
        } else {
          wrap(predicateAccess(loc.predicateName, "h", loc.args.map(rec(_, 0))), 100)
        }

      case ast.FuncApp(funcname, args) =>
        // Add implicit heap argument for heap-dep functions
        val og_fn = funcname.takeWhile(c => c != '$' && c != '%')
        val maybeHeap = obl.s.program.findFunctionOptionally(og_fn) match {
          case None => ""
          case Some(fn) => if (fn.isPure) "" else " " + domOldHeapLabel
        }
        wrap(safeString(funcname) + maybeHeap + args.map(a => " " + wrap(rec(a, 100), 100)).mkString(""), 100)
      case ast.DomainFuncApp(funcname, args, _) =>
        wrap(funcname + " " + args.map(rec(_, 100)).mkString(" "), 100)
      case ast.FieldAccess(rcv, field) =>
        val heapString = (for (oldLabel <- oldHeapLabel; keyLabel <- heapLabelMap.get(oldLabel.takeWhile(_ != '#')))
          yield printHeapLabel(keyLabel)).getOrElse("h")
          wrap(fieldAccess(field.name, heapString, rec(rcv, 100)), 100)

      case ast.CondExp(cond, thn, els) => "(if " + rec(cond, 10) + " then " + rec(thn, 10) +
        " else " + rec(els, 10) + ")"
      case ast.Unfolding(_, body) => rec(body, parenthesisLevel)
      case ast.Asserting(_, body) => rec(body, parenthesisLevel)
      case ast.Old(exp) => translateExp(exp, parenthesisLevel, renames, isFrameAxiom, variablePrime, resultString, Some("old"))
      case ast.LabelledOld(exp, oldLabel) =>
        translateExp(exp, parenthesisLevel, renames, isFrameAxiom, variablePrime, resultString, Some(oldLabel))
      case ast.DebugLabelledOld(exp, oldLabel) =>
        translateExp(exp, parenthesisLevel, renames, isFrameAxiom, variablePrime, resultString, Some(oldLabel))
      case ast.Let(variable, exp, body) =>
        wrap(s"let ${safeString(variable.name)} = ${rec(exp, 10)} in ${rec(body, 10)}", 10)
      case ast.Forall(vars, _, exp) =>
        val varRenames = vars.map(v => (v.name, cleanName(v)))
        val newRenames = renames ++ varRenames
        val varString = varRenames.map(_._2).mkString(" ")
        val bodyString = translateExp(exp, 10, newRenames, isFrameAxiom, variablePrime, resultString, oldHeapLabel)
        wrap(s"\\<forall>$varString. $bodyString", 10)
      case ast.Exists(variables, _, exp) =>
        wrap("\\<exists>" + variables.map(v => safeString(v.name)).mkString(" ") + ". " + rec(exp, 10), 10)
      case ast.LocalVar(name, _) =>
        val baseName = renames.getOrElse(name, safeString(name))
        baseName
      case ast.Result(_) => wrap(resultString.getOrElse("result"), 100)
      case ast.LocalVarWithVersion(name, _) if fieldReplacementsByName contains name =>
        val (chunk, heapLabel) = fieldReplacementsByName(name)
        wrap(basicFieldChunkLocation(chunk, heapLabel), 100)
      case ast.LocalVarWithVersion(name, _) =>
        renames.getOrElse(name, safeString(name))

      case ast.FullPerm() => "1"
      case ast.NoPerm() => "0"
      case ast.FractionalPerm(ast.IntLit(a), ast.IntLit(b)) =>
        if (a == b) "1"
        else if (a == 0) "0"
        else s"$a/$b"
      case ast.PermAdd(left, right) => recOp(left, "+", right, 65)
      case ast.PermSub(left, right) => recOp(left, "-", right, 65)
      case ast.PermMul(left, right) => recOp(left, "*", right, 70)
      case ast.PermLtCmp(left, right) => recOp(left, "<", right, 51)
      case ast.PermLeCmp(left, right) => recOp(left, "\\<le>", right, 51)
      case ast.PermGtCmp(left, right) => recOp(left, ">", right, 51)
      case ast.PermGeCmp(left, right) => recOp(left, "\\<ge>", right, 51)
      case ast.DebugPermMin(left, right) => wrap(s"min ${rec(left, 100)} ${rec(right, 100)}", 100)

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

      case todo => "TODO: " + todo.getClass + todo.toString
    }
  }

  private def translateDebugNode(debugNode: AnyDebugNode): Unit =
    translateDebugNode(debugNode, "", "", storeRenames, inAux = false)

  private def translateDebugNode(debugNode: AnyDebugNode, prefix: String, suffix: String,
                                renames: immutable.Map[String, String],
                                inAux: Boolean): Unit = {
    def recordPC(assumption: String): Unit = {
      val assumptionString = prefix + assumption + suffix
      if (!(printedAssumptions contains assumptionString)) {
        strings += s"  assumes ${debugNode.id}: \"$assumptionString\""
        printedAssumptions += assumptionString
      }
    }

    debugNode match {
      case debugExp: DebugExp if debugExp.isInternal =>
        if (debugExp.description.exists(_.contains("singleton-FVF"))) {
          strings += s"  assumes ${debugExp.id}: \"${translateTerm(debugExp.term)}\""
        }
        // do nothing TODO: do I need to keep the quantified precs?
      case debugExp: DebugExp if !debugExp.isInternal =>
        if (descriptionContains(debugExp, "perm")) {} // do nothing
        else if (descriptionContains(debugExp, "feasible")) {} // do nothing
        else if (inAux && descriptionContains(debugExp, "branch")) {} // do nothing
        else {
          debugExp.finalExp match {
            case Some(_: PermLeCmp) | Some(_: PermLtCmp) | Some(_: PermGeCmp) | Some(_: PermGtCmp) => // do nothing
            case _ =>
              recordPC(translateExp(debugExp.finalExp.getOrElse(debugExp.originalExp.get), renames = renames))
              // strings += s"  assumes ${debugExp.id}: \"$prefix$assumptionString$suffix\""
          }
        }
      case varDef: FreshVarDefinition =>
        if (usedVarDefinitions contains varDef)
          recordPC(translateExp(varDef.finalExp.get, renames = renames))
      case debugPre: DebugPrecondition =>
        val function = program.findFunction(debugPre.funExp.funcname)
        if (function.pres.nonEmpty) {
          val domHeapLabel = if (!function.isPure)
            printHeapLabel(heapLabelMap.getOrElse(debugPre.heapLabel, debugPre.heapLabel)) + " "
          else ""
          val assumptionString = s"${debugPre.funExp.funcname}_pre $domHeapLabel" +
            debugPre.finalArgs.get.map(translateExp(_, parenthesisLevel = 100, renames = renames)).mkString(" ")
          recordPC(assumptionString)
        }
      case quantifier: DebugQuantifier =>
        val varRenames = quantifier.qvars.map(v => (v.toString, v.toString.takeWhile(c => c != '@' && c != '$')))
        val newRenames = renames ++ varRenames
        val qvarString = "\\<forall>" + varRenames.map(_._2).mkString(" ") + ". "
        quantifier.children.toSeq.sortBy(_.id) foreach {
          translateDebugNode(_, prefix + qvarString, suffix, newRenames, inAux = inAux) }
      case implication: DebugImplication =>
        val LHS = if (implication.isInternal) translateTerm(implication.term, renames = renames)
          else translateExp(implication.finalExp.get, renames = renames)
        implication.children.toSeq.sortBy(_.id) foreach {
          translateDebugNode(_, prefix + s"$LHS \\<longrightarrow> (", ")" + suffix, renames, inAux = inAux) }
      case invariant: DebugInvariant =>
        strings += s"  (* Begin loop invariant at ${invariant.loopPos} *)"
        invariant.children.toSeq.sortBy(_.id) foreach { translateDebugNode(_, prefix, suffix, renames, inAux) }
        strings += "  (* End loop invariant *)"
      case group: DebugGroup if group.groupDescription.contains("unfolding of") => // do nothing
      case group: DebugGroup =>
        val isAuxGroup = inAux || group.description.getOrElse("").contains("aux")
        group.children.toSeq.sortBy(_.id) foreach { translateDebugNode(_, prefix, suffix, renames, inAux = isAuxGroup) }
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
    val eSimp = Simplifier.simplify(e)
    val collapsed = collapseCondExp(eSimp)
    val collapsedSimp = Simplifier.simplify(collapsed)
    val posExp = posExpCond(collapsedSimp)
    Simplifier.simplify(posExp)
  }

  def permIsPositive(e: Exp): Boolean = {
    posExpCond(e) match {
      case _: ast.TrueLit => true
    }
  }

  // Silicon permissions are largely of the form (c ? p : Z)
  // If these are nested we collapse them to simplify
  private def collapseCondExp(p: Exp): Exp = {
    p match {
      case ast.CondExp(c0, ast.CondExp(c1, p1, ast.NoPerm()), ast.NoPerm()) =>
        collapseCondExp(ast.CondExp(ast.And(c0, c1)(), p1, ast.NoPerm()())())
      case ast.CondExp(c, p0, p1) => ast.CondExp(c, collapseCondExp(p0), collapseCondExp(p1))()
      case ast.PermSub(ast.CondExp(c, thn, els), a) =>
        val newThn = ast.PermSub(thn, a)()
        val newEls = ast.PermSub(els, a)()
        collapseCondExp(ast.CondExp(c, newThn, newEls)())
      case ast.PermSub(a, ast.CondExp(c, thn, els)) =>
        val newThn = ast.PermSub(a, thn)()
        val newEls = ast.PermSub(a, els)()
        collapseCondExp(ast.CondExp(c, newThn, newEls)())
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
      case _ => Simplifier.simplify(ast.PermLtCmp(p, ast.FullPerm()())())
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

  def cleanName(v: ast.LocalVarDecl): String =
    v.name.takeWhile(c => c != '@' && c != '$')

  def argStringWithTypes(vars: Seq[ast.LocalVarDecl], includeHeap: Boolean): String =
    (if (includeHeap) "(h::Heap) " else "") +
      vars.map(v => s"(${cleanName(v)}::${translateType(v.typ)})").mkString(" ")

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

  def getPrecPropagationExp(fn: ast.Function, p: Program): Option[Exp] = {
    fn.body match {
      case None => None
      case Some(body) =>
        val bodyExp = Simplifier.simplify(preconditionPropagationExp(body, p))
        bodyExp match {
          case ast.TrueLit() => None
          case _ =>
            if (fn.pres.nonEmpty) {
              val argsExps = fn.formalArgs.map(a =>
                ast.LocalVar(a.name, a.typ)(a.pos, a.info, a.errT)
              )
              val fnPre = ast.FuncApp(fn.name+"$_pre", argsExps)(fn.pos, fn.info, ast.Bool, fn.errT)
              Some(ast.Implies(fnPre, bodyExp)())
            } else {
              Some(bodyExp)
            }
        }
    }
  }

  /** Follows the same logic as silicon.FunctionPreconditionTransformer.transform
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
          case _ => ast.Forall(variables, triggers, exp = body2)(e.pos, e.info, e.errT)
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

  def descriptionContains(debugNode: AnyDebugNode, string: String): Boolean = {
    debugNode.description match {
      case Some(desc) => desc.toLowerCase().contains(string.toLowerCase())
      case None => false
    }
  }

  // Note, will remove Trues
  private def bigAnd(es: Seq[Exp], pos: ast.Position, info: ast.Info, errT: ast.ErrorTrafo): Exp = {
    val filtered = es.filterNot(_.isInstanceOf[ast.TrueLit])
    if (filtered.isEmpty) ast.TrueLit()(pos, info, errT)
    else if (filtered.length == 1) filtered.head
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

  def localeName(m: MemberSeq): String = m.head.name + m.tail.map(_.name).mkString("_")

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

  // Maps each debug heap label to its dominant heap label, possibly itself.
  // E.g. all heaps generated while inhaling preconditions are dominated by "old".
  def heapLabelMap(debugHeaps: DebugOldHeaps, tempHeaps: Option[TemporaryRecord]): Map[String, String] = {
    def isFold(heapCause: HeapCause): Boolean = {
      heapCause match {
        case ExecStmt(s) => s match {
          case _: ast.Fold
               | _: ast.Unfold => true
          case _ => false
        }
        case _ => false
      }
    }

    // follows fold/unfold parents
    def equiParent(label: String): String = {
      val heapRecord = debugHeaps(label)
      if (isFold(heapRecord.cause)) equiParent(heapRecord.parentLabel) else label
    }

    // Maps key heaps to their labelled children, when relevant, including old heaps
    val labelledHeapsMap = debugHeaps.collect {
      case (label, record) if record.cause == CreateLabel && equiParent(label).contains("debug@") =>
        (equiParent(label), label)
    } ++ debugHeaps.collect {
      case (label, record) if record.cause == InhalePre =>
        (label, Verifier.PRE_STATE_LABEL)
    }

    // if a key heap is dominated by a label, use that, otherwise use the equiparent
    val keyHeapMap = debugHeaps.collect {
      case (label, _) => (label, labelledHeapsMap.getOrElse(label, equiParent(label)))
    }

    // Maps every intermediate heap to the dominator of its key heap
    val intermediateHeapMap = debugHeaps.flatMap { case (keyLabel, record) =>
      record.intermediateHeaps.map { case (interLabel, _) =>
        (interLabel, keyHeapMap(keyLabel))
      }
    }

    // TODO: I think this should always be empty for regular asserts?
    val tempIntermediates = tempHeaps match {
      case Some((_, _, _, heaps)) => heaps.map(kv => (kv._1, kv._1))
      case None => Map.empty[String, String]
    }

    val result = tempIntermediates ++ keyHeapMap ++ intermediateHeapMap
    result
  }
}
