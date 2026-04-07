package viper.silicon.debugger

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.debugger.ExportUtils._
import viper.silicon.debugger.Rewrites.{addRename, addRenames, emptyRewrites}
import viper.silicon.state
import viper.silicon.state.{Identifier, terms}
import viper.silicon.state.terms.{Sort, Term, sorts}
import viper.silicon.resources
import viper.silicon.resources.{FieldID, PredicateID}
import viper.silicon.state.terms.sorts.Snap
import viper.silver.ast
import viper.silver.ast.{Domain, DomainAxiom, FuncLike}
import viper.silver.utility.Common.Rational

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Paths}
import scala.collection.mutable.ArrayBuffer
import scala.collection.{immutable, mutable}
import scala.io.StdIn.readLine


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
          println("Overwriting file...")
        } else {
          println("Did not export")
          return
        }
      } else {
        println("Exporting to file...")
        Files.createFile(filepath)
      }

      // Write to file
      val writer = Files.newBufferedWriter(filepath, StandardCharsets.UTF_8)
      val filename = filepath.getFileName.toString.split('.')(0)
      val t = new Translator(obl, filename)
      t.translateObligation()
      t.strings.foreach(s => writer.write(s + "\n"))
      writer.close()

    } catch {
      case e: Throwable =>
        println("Error exporting to Isabelle")
        throw e
    }
  }
}

// Things to rewrite as you translate terms
case class Rewrites(varRenames: immutable.Map[state.Identifier, String],
                    termReplacements: immutable.Map[Term, String])

object Rewrites {
  def apply(varRenames: immutable.Map[state.Identifier, String],
            termReplacements: immutable.Map[Term, String]): Rewrites = {
    new Rewrites(varRenames, termReplacements)
  }

  val emptyRewrites: Rewrites = Rewrites(Map(), Map())

  def addRename(rewrites: Rewrites, id: Identifier, rep: String): Rewrites = {
    Rewrites(rewrites.varRenames + (id -> rep), rewrites.termReplacements)
  }

  def addRenames(rewrites: Rewrites, toAdd: Map[Identifier, String]): Rewrites = {
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
  private val basicRewrites: Rewrites = { // Rewrites(renaming2, immutable.Map())
    // Add local vars from the store
    val varRenames = mutable.Map[state.Identifier, String]()
    for ((lVar, term) <- obl.s.g.termValues) {
      term match {
        case terms.Var(id, _, _) =>
          if (!(varRenames contains id)) {
            varRenames += id -> safeString(lVar.toString) // add if non-existent
          } else if (idHead(id) == lVar.name) {
            varRenames(id) = safeString(lVar.toString) // update if better match found
          }
        case _ => println(s"Store entry is not a Var: $lVar -> $term")
      }
    }
    // Add location variables from the heap
    val termReps = mutable.Map[Term, String]()
    val varRewrites = Rewrites(varRenames.toMap, Map())
    for ((label, heap) <- obl.s.oldHeaps) {
      for (chunk <- heap.values) {
        chunk match {
          case bc: state.BasicChunk =>
            bc.resourceID match {
              // If the chunk is a basic field access, add renaming
              case resources.FieldID =>
                if (termReps contains bc.snap) {
                  println(s"Snap already in termReps: reading ${bc.toString}, but ${bc.snap} is ${termReps(bc.snap)}")
                }
                else if (permIsPositive(bc.perm)) {
                  val fieldLabelString = if (label == currentHeapLabel) bc.id.name else s"${bc.id}' ${safeString(label)}"
                  termReps += bc.snap -> (fieldLabelString + " " + translateTerm(bc.args.head, rewrites = varRewrites))
                } else ()
              case _ =>
            }
          case _ => // TODO: Can we add snapshot maps to rewrites? Carry around the condition?
        }
      }
    }
    Rewrites(varRenames.toMap, termReps.toMap)
  }

  // TODO: Not sure if safe, this assumes correct key insertion order???
  // Maybe check it equals current heap, modulo unfolding?
  private val currentHeapLabel: String = obl.s.oldHeaps.keys.last

  def translateObligation(): Unit = {
    strings += s"theory $filename\n"
    strings += "imports \"~/Viper/isabelle/ViperTranslations\"\n"
    strings += "begin\n\n"

    declareDomainTypes()
    defineHeaps()
    translateDomainsFunctionsPredicates()
    generateLemma()

    strings += "end"
  }

  private def declareDomainTypes(): Unit = {
    // First declare domain types
    if (domains.nonEmpty) {
      strings += "text \\<open>Declare domain types\\<close>\n"
      domains.foreach(d => strings += "typedecl " + d._1.name)
      strings += "\n"
    }
  }

  private def defineHeaps(): Unit = {
    strings += "text \\<open>Define fields and heaps\\<close>\n"
    strings += "locale Heaps ="
    if (obl.s.program.fields.nonEmpty) {
      strings += "  (* Fields *)"
      val fieldLength = obl.s.program.fields.map(_.name.length).max
      for (fld <- obl.s.program.fields) {
        val nameString = padString(safeString(fld.name) + "'", fieldLength+1)
        strings += s"  fixes $nameString :: \"Heap $FN_ARR ref $FN_ARR ${translateType(fld.typ)}\""
      }
    }
    strings += "  (* Old heaps *)"
    val heapLabelLength = obl.s.oldHeaps.keys.map(_.length).max
    for (h <- obl.s.oldHeaps) {
      strings += s"  fixes ${padString(safeString(h._1), heapLabelLength)} :: Heap"
    }
    strings += ""

    // Abbreviate fields
    if (obl.s.program.fields.nonEmpty) {
        strings += "context Heaps\nbegin\n"
        val currentLabel = safeString(currentHeapLabel)
        for (f <- obl.s.program.fields) {
          strings += s"abbreviation ${f.name} :: \"ref $FN_ARR ${translateType(f.typ)}\" where"
          strings += s"  \"${f.name} r \\<equiv> ${f.name}' $currentLabel r\"\n"
        }
        strings += "end\n"
    }
    strings += ""
  }

  private def translateDomainsFunctionsPredicates(): Unit = {
    strings += "text \\<open>Translated domains and functions\\<close>\n"
    val (independentDomains, dependentDomains) = domains.partition(domDeps => DomainDeps.isSelfContained(domDeps._1))

    def functionType(fn: FuncLike, isPrecondition: Boolean = false, isHeapDep: Boolean = false): String = {
      val name = if (isPrecondition) fn.name + "_pre" else fn.name
      val maybeHeap = if (isHeapDep) s"Heap $FN_ARR " else ""
      val argString = fn.formalArgs.map(a => translateType(a.typ) + s" $FN_ARR ").mkString("")
      val typeString = if (isPrecondition) "bool" else translateType(fn.typ)
      name + " :: \"" + maybeHeap + argString + typeString + "\""
    }

    def translateAxiom(ax: DomainAxiom): String = {
      val axName = ax match {
        case ast.NamedDomainAxiom(name, _) => name + ": "
        case _ => ""
      }
      s"  assumes $axName\"${translateExp(ax.exp)}\""
    }

    for (d <- independentDomains) {
      strings += s"locale ${d._1.name}_Domain ="
      d._1.functions.foreach(fn => strings += s"  fixes " + functionType(fn))
      //for (ax <- d._1.axioms) { strings += s"  assumes ${axiomName(ax)}: \"${translateExp(ax.exp)}\"" }
      d._1.axioms.foreach { strings += translateAxiom(_) }
      strings += ""
    }

    for (d <- dependentDomains) {
      strings += s"locale ${d._1.name}_Functions ="
      d._1.functions.foreach(fn => strings += s"  fixes " + functionType(fn))
      strings += ""
    }

    // Program functions
    strings += "locale Program_Functions ="
    if (obl.s.program.functions.isEmpty) {
      strings += "  assumes True (* no functions to translate *)\n"
    } else {
      for (fn <- obl.s.program.functions) {
        if (fn.pres.nonEmpty) {
          strings += s"  fixes " + functionType(fn, isPrecondition = true, isHeapDep = !fn.isPure)
        }
        strings += s"  fixes " + functionType(fn, isHeapDep = !fn.isPure)
      }
      strings += ""
    }

    // Pure part of predicates
    strings += "locale Predicates ="
    if (obl.s.program.predicates.isEmpty) {
      strings += "  assumes True (* no predicates to translate *)\n"
    } else {
      for (pred <- obl.s.program.predicates) {
        val typeString = s"Heap $FN_ARR " + pred.formalArgs.map(a => translateType(a.typ) + s" $FN_ARR ").mkString("")
        strings += s"  fixes ${pred.name} :: \"${typeString}bool\""
        val typeTuple = s"Heap \\<times> ${pred.formalArgs.map(a => translateType(a.typ)).mkString(" \\<times> ")}"
        strings += s"  fixes ${pred.name}_eq :: \"$typeTuple $FN_ARR $typeTuple $FN_ARR bool\""
      }
      strings += ""
    }

    // Create combined locale
    strings += "locale Program = Heaps + Program_Functions + Predicates +"
    independentDomains.foreach(d => strings += s"  ${d._1.name}_Domain +")
    dependentDomains.foreach(d => strings += s"  ${d._1.name}_Functions +")

    val noAxioms = domains.forall(_._1.axioms.isEmpty)
    if (obl.s.program.functions.isEmpty && noAxioms) {
      strings += "  assumes True (* No function definitions/axioms *)"
      // We could return here with a blank line?? But should be no different.
    }

    // Domain axioms
    for (d <- dependentDomains) {
      strings += s"  (* ${d._1.name} domain axioms *)"
      //for (ax <- d._1.axioms) strings += s"  assumes ${axiomName(ax)}: \"${translateExp(ax.exp)}\""
      d._1.axioms.foreach { strings += translateAxiom(_) }
    }

    // Function definitions
    strings += "  (* Function definitions and posts *)"
    obl.s.program.functions.foreach(translateFunctionDef)
    strings += "  (* Predicate properties *)"
    obl.s.program.predicates.foreach(translatePredicate)
    strings += "\n"
  }

  private def translateFunctionDef(fn: ast.Function): Unit = {
    val argString = (if (fn.isPure) "" else "h ") + fn.formalArgs.map(_.name).mkString(" ")
    val argStringWTypes = (if (fn.isPure) "" else "h ") + fn.formalArgs.map(a => s"(${a.name}::${translateType(a.typ)})").mkString(" ")

    // Translate function body
    if (fn.body.isDefined) {
      val fnRHS = "(" + translateExp(fn.body.get) + ")"
      if (fn.pres.isEmpty) {
        strings += s"  assumes ${fn.name}_def: \"\\<And>$argString. ${fn.name} $argString =\n    $fnRHS\""
      } else {
        strings += s"  assumes ${fn.name}_def: \"\\<And>$argString. " +
          s"${fn.name}_pre $argString $META_ARR ${fn.name} $argString =\n    $fnRHS\""
      }
      // Translate internal function calls
      extractPropagation(fn.name) match {
        case None =>
        case Some((_, terms.True)) =>
        case Some((vars, body)) =>
          var newRenames = vars.tail.map(v => (v.id, v.id.name.takeWhile(_ != '@'))).toMap
          if (!fn.isPure) newRenames = newRenames + (vars.head.id -> "h")
          val newRewrites = addRenames(basicRewrites, newRenames)
          def translate: Term => String = translateTerm(_, 50, newRewrites, options = defaultOptions.collapseSnapsOn())

          val bodyString = body match {
            case terms.Implies(p0, p1) => s"${translate(p0)} $META_ARR ${translate(p1)}"
            case _ => translate(body)
          }
          //val propString = translateTerm(prop, newRewrites, collapseSnaps = true).replace("NO_HEAP", "h")
          // TODO: use argString and fix variables with unnecessary suffixes
          strings += s"  assumes ${fn.name}_calls: \"\\<And>$argStringWTypes. ${bodyString.replace("NO_HEAP", "h")}\""
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
      val argStringH2 = "h2" + argString.drop(1)
      val footprint = fn.pres.filter(!_.isPure).map(translateExp(_, parenthesisLevel = 35, isFrameAxiom = true)).mkString(" \\<and> ")
      strings += s"  assumes ${fn.name}_framing: \"\\<And>h1 $argStringH2. " +
        s"${fn.name}_pre $argStringH1 \\<and> ${fn.name}_pre $argStringH2"
      strings += s"    \\<and> $footprint"
      strings += s"    $META_ARR ${fn.name} $argStringH1 = ${fn.name} $argStringH2\""
    }
  }

  // For an axiom of the form QA vars :: prop, extracts vars and prop
  private def extractPropagation(fn: String): Option[(Seq[terms.Var], Term)] = {
    val propAx = obl.s.functionData(fn).bodyPreconditionPropagationAxiom
    propAx match {
      case Seq(t) => t match {
        case q: terms.Quantification => Some((q.vars, q.body))
      }
      case _ => None
    }
  }

  private def translatePredicate(pred: ast.Predicate): Unit = {
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
        val varsString = "h1 h2 " + pred.formalArgs.map(a => s"${a.name} ${a.name}'").mkString(" ")
        val argString1 = s"(h1, ${pred.formalArgs.map(_.name).mkString(", ")})"
        val argString2 = s"(h1, ${pred.formalArgs.map(_.name + "'").mkString(", ")})"
        val bodyString = translateExp(exp, parenthesisLevel = 51, isFrameAxiom = true)
        strings += s"  assumes ${pred.name}_eq_def: \"\\<And>$varsString. ${pred.name}_eq $argString1 $argString2 $META_ARR"
        strings += s"    $bodyString\""
      case None =>
    }
  }

  private def generateLemma(): Unit = {
    strings += "text \\<open>Proof obligation\\<close>\n"
    strings += "context Program\nbegin\n\nlemma"
    translateStore()
    translateHeaps()
    strings += "  (* Assumptions *)"
    obl.assumptionsExp.foreach(translateDebugExp(_))

    // val assertionTerm = obl.eAssertion.term.getOrElse(obl.assertion)
    strings += "  shows \"" + translateTerm(obl.assertion) + "\""
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
    obl.s.oldHeaps.foreach { case (label, heap) => translateHeap(heap, label) }
  }

  private def translateHeap(h: state.Heap, label: String): Unit = {
    if (label == currentHeapLabel)
      strings += "  (* Current heap *)"
    else
      strings += s"  (* Heap $label *)"
    for ((c, idx) <- h.values.zipWithIndex) {
      c match {
        case bc: state.BasicChunk =>
          bc.resourceID match {
            case FieldID =>
              if (bc.args.length == 1) {
                val ref = translateTerm(bc.args.head, parenthesisLevel = 100)
                val permCondition = permCondSimp(bc.perm)
                val condString = if (permCondition == terms.True) "" else translateTerm(permCondition) + s" $META_ARR "
                val field = if (label == currentHeapLabel) s"${bc.id.name} $ref" else s"${bc.id.name}' ${safeString(label)} $ref"
                val chunk = s"$condString$field = ${translateTerm(bc.snap)}"
                strings += s"  assumes ${safeString(label)}_$idx: \"$chunk\""
              } else {
                strings += s"  (* Error: $bc has wrong args *)"
              }
            case PredicateID =>
              val chunk = safeString(bc.id.name) + s" ${safeString(label)} " +
                bc.args.map(translateTerm(_, parenthesisLevel = 100)).mkString(" ")
              strings += s"  assumes ${safeString(label)}_$idx: \"$chunk\""
          }
        case qfc: state.QuantifiedFieldChunk =>
          val permCondition = terms.And(qfc.condition, permCondSimp(qfc.permValue))
          val condString = translateTerm(permCondition) + s" $META_ARR"
          val field = if (label == "curr") s"${qfc.id.name} r" else s"${qfc.id.name}_' (${safeString(label)} r)"
          val chunk = s"\\<And>r. $condString $field = ${qfc.id}_${translateTerm(qfc.fvf)} r"
          strings += s"  assumes ${safeString(label)}_$idx: \"$chunk\""
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
  private def translateTerm(term: terms.Term,
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
      case terms.Var(id, _, _) => rewrites.varRenames getOrElse(id, safeId(id))
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
          if (rewrites.varRenames.contains(v.id)) rewrites.varRenames(v.id)
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
      case terms.EmptySet(_) => "{}\\<^sup>+"
      case terms.SingletonSet(elem) => s"{${rec(elem, 0)}}\\<^sup>+"
      case terms.SetAdd(left, right) => wrap(s"insert_fin ${rec(right, 100)} ${rec(left, 100)}", 100)
      case terms.SetUnion(left, right) => recOp(left, "\\<union>\\<^sup>+", right, 65)
      case terms.SetIntersection(left, right) => recOp(left, "\\<inter>\\<^sup>+", right, 70)
      case terms.SetSubset(left, right) => recOp(left, "\\<subset>\\<^sup>+", right, 75)
      case terms.SetDisjoint(left, right) => wrap(s"disjnt_finset ${rec(left, 100)} ${rec(right, 100)}", 100)
      case terms.SetDifference(left, right) => recOp(left, "-", right, 65)
      case terms.SetIn(elem, set) => recOp(elem, "\\<in>\\<^sup>+", set, 51)
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
      case terms.EmptyMap(_, _) => "Map.empty"
      case terms.MapLookup(base, key) => wrap(rec(base, 100) + "@@" + rec(key, 100), 100)
      case terms.MapCardinality(map) => "card\\<^sub>Z (dom " + rec(map, 100) + ")"
      case terms.MapUpdate(map, key, value) => rec(map, 100) + "(" + rec(key, 100) + "\\<mapsto>" + rec(value, 100) + ")"
      case terms.MapDomain(map) => wrap(s"dom ${rec(map, 100)}", 100)
      case terms.MapRange(map) => wrap(s"ran ${rec(map, 100)}", 100)
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
      //case _ => term.getClass.toString + term.toString
    }
    //"error or missing term case"
  }

  def translateType(t: ast.Type): String = {
    t match {
      case ast.Int => "int"
      case ast.Bool => "bool"
      case ast.Perm => "perm" // TODO: maybe remove? Or make unit/error
      case ast.Ref => "ref"
      case ast.SeqType(elem) => translateType(elem) + " list"
      case ast.SetType(elem) => translateType(elem) + " finset"
      case ast.MultisetType(elementType) => translateType(elementType) + " multiset"
      case ast.DomainType(name, vars) => name
      case ast.TypeVar(name) => "'" + name.toLowerCase()
      case _ => "other_type"
    }
  }

  private def translateSort(sort: Sort): String = {
    sort match {
      case sorts.Snap => "error: Snap sort"
      case sorts.Int => "int"
      case sorts.Bool => "bool"
      case sorts.Ref => "ref"
      case sorts.Perm => "perm"
      case sorts.Unit => "unit"
      case sorts.Seq(elementsSort) => translateSort(elementsSort) + " list"
      case sorts.Set(elementsSort) => translateSort(elementsSort) + " set"
      case sorts.Multiset(elementsSort) => translateSort(elementsSort) + " multiset"
      case sorts.Map(keySort, valueSort) => "TODO: Map" // TODO
      case sorts.UserSort(id) => safeString(id.name)
      case sorts.SMTSort(id) => safeString(id.name)
      case sorts.FieldValueFunction(codomainSort, _) => "" // TODO
      case sorts.PredicateSnapFunction(codomainSort, _) => "" // TODO
      case sorts.MagicWandSnapFunction => "" // TODO
      case sorts.FieldPermFunction() => "" // TODO
      case sorts.PredicatePermFunction() => "" // TODO
    }
  }

  def translateFunType(fn: ast.FuncLike): String = {
    "" // TODO
  }

  private def setPostfix(t: ast.Type): String = {
    t match {
      case _: ast.SetType => "\\<^sup>+"
      case _: ast.MultisetType => "#"
    }
  }

  private def translateExp(e: ast.Exp,
                           parenthesisLevel: Int = 0,
                           isFrameAxiom: Boolean = false,
                           variablePrime: Boolean = false,
                           resultString: Option[String] = None): String = {
    def rec(e2: ast.Exp, pLevel: Int): String = translateExp(e2, pLevel, isFrameAxiom, variablePrime, resultString)
    def wrap(s: String, pLevel: Int): String = if (pLevel <= parenthesisLevel) s"($s)" else s
    def recOp(left: ast.Exp, op: String, right: ast.Exp, pLevel: Int): String = {
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
          s"${loc.field.name}' h1 $loc1 = ${loc.field.name}' h2 $loc2"
        }
        else "undefined"
      case ast.PredicateAccessPredicate(loc, _) =>
        if (isFrameAxiom){
          val argString1 = loc.args.map(rec(_, 100)).mkString(", ")
          val argString2 = loc.args.map(
            translateExp(_, parenthesisLevel, isFrameAxiom, variablePrime = true, resultString)
          ).mkString(", ")
          s"${loc.predicateName}_eq (h1, $argString1) (h2, $argString2)"
        } else {
          val argString = loc.args.map(rec(_, 100)).mkString(" ")
          wrap(s"${loc.predicateName} h $argString", 100)
        }

      case ast.FuncApp(funcname, args) =>
        // Add implicit heap argument for heap-dep functions
        val maybeHeap = if (obl.s.program.findFunction(funcname).isPure) "" else " h"
        wrap(funcname + maybeHeap + args.map(a => " " + rec(a, 100)).mkString(""), 100)
      case ast.DomainFuncApp(funcname, args, _) =>
        wrap(funcname + " " + args.map(rec(_, 100)).mkString(" "), 100)
      case ast.FieldAccess(rcv, field) => wrap(s"${field.name}' h ${rec(rcv, 100)}", 100)

      case ast.CondExp(cond, thn, els) => "(if " + rec(cond, 10) + " then " + rec(thn, 10) +
        " else " + rec(els, 10) + ")"
      case ast.Unfolding(_, body) => rec(body, parenthesisLevel)
      case ast.Asserting(_, body) => rec(body, parenthesisLevel)
      case ast.Let(variable, exp, body) =>
        s"let ${safeString(variable.name)} = ${rec(exp, 10)} in ${rec(body, 10)}"
      case ast.Forall(variables, _, exp) =>
        wrap("\\<forall>" + variables.map(v => safeString(v.name)).mkString(" ") + ". " + rec(exp, 10), 10)
      case ast.Exists(variables, _, exp) =>
        wrap("\\<exists>" + variables.map(v => safeString(v.name)).mkString(" ") + ". " + rec(exp, 10), 10)
      case ast.LocalVar(name, _) => if (variablePrime) safeString(name) + "'" else safeString(name)
      case ast.Result(_) => wrap(resultString.getOrElse("result"), 100)
      case ast.LocalVarWithVersion(name, _) => if (variablePrime) safeString(name) + "'" else safeString(name)

      case ast.EmptySeq(_) => "[]"
      case ast.ExplicitSeq(elems) => "[" + elems.map(rec(_, 0)).mkString(", ") + "]"
      case ast.RangeSeq(low, high) => s"[${rec(low, 0)}..${rec(high, 0)}]"
      case ast.SeqAppend(left, right) => recOp(left, "@", right, 65)
      case ast.SeqIndex(s, idx) => recOp(s, "!\\<^sub>Z", idx, 100)
      case ast.SeqTake(s, n) => wrap("take\\<^sub>Z " + rec(n, 100) + " " + rec(s, 100), 100)
      case ast.SeqDrop(s, n) => wrap("drop\\<^sub>Z " + rec(n, 100) + " " + rec(s, 100), 100)
      case ast.SeqContains(elem, s) => recOp(elem, "\\<in>:", s, 51)
      case ast.SeqUpdate(s, idx, elem) => wrap(s"list_update ${rec(s, 100)} ${rec(idx, 100)} ${rec(elem, 100)}", 100)
      case ast.SeqLength(s) => wrap("length\\<^sub>Z " + rec(s, 100), 100)

      case ast.EmptySet(_) => "{}\\<^sup>+"
      case ast.ExplicitSet(elems) => "{" + elems.map(rec(_, 0)).mkString(", ") + "}\\<^sup>+"
      case ast.EmptyMultiset(_) => "{#}"
      case ast.ExplicitMultiset(elems) => "{#" + elems.map(rec(_, 0)).mkString(", ") + "#}"
      case ast.AnySetUnion(left, right) =>
        wrap(rec(left, 65) + s" \\<union>${setPostfix(left.typ)} " + rec(right, 65), 65)
      case ast.AnySetIntersection(left, right) =>
        rec(left, 70) + s" \\<inter>${setPostfix(left.typ)} " + rec(right, 70)
      case ast.AnySetSubset(left, right) =>
        wrap(rec(left, 75) + s" \\<subset>${setPostfix(left.typ)} " + rec(right, 75), 75)
      case ast.AnySetMinus(left, right) => recOp(left, "-", right, 65)
      case ast.AnySetContains(elem, s) => recOp(elem, s"\\<in>${setPostfix(s.typ)}", s, 51)
      case ast.AnySetCardinality(s) =>
        s.typ match {
          case _: ast.SetType => "card\\<^sub>Z " + rec(s, 100)
          case _: ast.MultisetType => "size\\<^sub>Z " + rec(s, 100)
        }

      case ast.EmptyMap(_, _) => "empty_finmap"
      case ast.ExplicitMap(elems) => "" //TODO
      case ast.Maplet(key, value) => s"[${rec(key, 0)}\\<mapsto>${rec(value, 0)}]\\<^sup>+"
      case ast.MapUpdate(base, key, value) => "" // TODO
      case ast.MapContains(key, base) => recOp(key, "\\<in>m", base, 46)
      case ast.MapCardinality(base) => "finmap_card " + rec(base, 100)
      case ast.MapDomain(base) => "dom_finmap " + rec(base, 100)
      case ast.MapRange(base) => "ran_finmap " + rec(base, 100)

      case todo => "TODO: " + todo.toString
    }
  }

  // TODO: Can we swap this for the finalExp from de?
  private def termExpMatch(term: terms.Term, exp: ast.Exp): Boolean = {
    (term, exp) match {
      case (terms.App(name, argsT, _), ast.FuncApp(funcname, argsE)) => name.id.name == funcname
      case (terms.SetIn(elemT, setT), ast.AnySetContains(elemE, setE)) => true
      case (terms.SeqIn(_, _), ast.SeqContains(_, _)) => true
      case _ => false
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

  // Set of domain names and program function names that a domain refers to
  case class DomainDeps(domains: Set[String], functions: Set[String]) {
    def ++(more: DomainDeps): DomainDeps = DomainDeps(domains ++ more.domains, functions ++ more.functions)
  }

  object DomainDeps {
    def empty = DomainDeps(Set(), Set())
    def singleD(domName: String): DomainDeps = DomainDeps(Set(domName), Set())
    def singleF(funName: String): DomainDeps = DomainDeps(Set(), Set(funName))
    def concat(dds: Seq[DomainDeps]): DomainDeps = dds.foldLeft(DomainDeps.empty)(_ ++ _)
    def isSelfContained(dom: ast.Domain): Boolean = getDomainDeps(dom) == DomainDeps(Set(dom.name), Set())
  }

  def getDomainDeps(dom: ast.Domain): DomainDeps = {
    DomainDeps.concat(dom.axioms.map(ax => domainDepsIn(ax.exp)))
  }

  private def domainDepsIn(e: ast.Exp): DomainDeps = {
    e match {
      case ast.Add(left, right) => domainDepsIn(left) ++ domainDepsIn(right)
      case ast.Sub(left, right) => domainDepsIn(left) ++ domainDepsIn(right)
      case ast.Mul(left, right) => domainDepsIn(left) ++ domainDepsIn(right)
      case ast.Div(left, right) => domainDepsIn(left) ++ domainDepsIn(right)
      case ast.Mod(left, right) => domainDepsIn(left) ++ domainDepsIn(right)
      case ast.LtCmp(left, right) => domainDepsIn(left) ++ domainDepsIn(right)
      case ast.LeCmp(left, right) => domainDepsIn(left) ++ domainDepsIn(right)
      case ast.GtCmp(left, right) => domainDepsIn(left) ++ domainDepsIn(right)
      case ast.GeCmp(left, right) => domainDepsIn(left) ++ domainDepsIn(right)
      case ast.EqCmp(left, right) => domainDepsIn(left) ++ domainDepsIn(right)
      case ast.NeCmp(left, right) => domainDepsIn(left) ++ domainDepsIn(right)

      case ast.IntLit(_) => DomainDeps.empty
      case ast.Minus(exp) => domainDepsIn(exp)
      case ast.Or(left, right) => domainDepsIn(left) ++ domainDepsIn(right)
      case ast.And(left, right) => domainDepsIn(left) ++ domainDepsIn(right)
      case ast.Implies(left, right) => domainDepsIn(left) ++ domainDepsIn(right)
      case ast.MagicWand(left, right) => domainDepsIn(left) ++ domainDepsIn(right)
      case ast.Not(exp) => domainDepsIn(exp)
      case ast.TrueLit() => DomainDeps.empty
      case ast.FalseLit() => DomainDeps.empty
      case ast.NullLit() => DomainDeps.empty

      case ast.FuncApp(funcname, args) => DomainDeps.singleF(funcname) ++ DomainDeps.concat(args.map(domainDepsIn))
      case ast.DomainFuncApp(funcname, args, _) =>
        val domName = obl.s.program.findDomainFunction(funcname).domainName
        DomainDeps.singleD(domName) ++ DomainDeps.concat(args.map(domainDepsIn))
      case ast.FieldAccess(rcv, _) => domainDepsIn(rcv)

      case ast.CondExp(cond, thn, els) => domainDepsIn(cond) ++ domainDepsIn(thn) ++ domainDepsIn(els)
      case ast.Let(_, exp, body) => domainDepsIn(exp) ++ domainDepsIn(body)

      case ast.Forall(_, _, exp) => domainDepsIn(exp)
      case ast.Exists(_, _, exp) => domainDepsIn(exp)
      case _: ast.LocalVar => DomainDeps.empty
      case _: ast.Result => DomainDeps.empty
      case _: ast.LocalVarWithVersion => DomainDeps.empty

      case _: ast.EmptySeq => DomainDeps.empty
      case _: ast.ExplicitSeq => DomainDeps.empty
      case _: ast.RangeSeq => DomainDeps.empty
      case ast.SeqAppend(left, right) => domainDepsIn(left) ++ domainDepsIn(right)
      case ast.SeqIndex(s, idx) => domainDepsIn(s) ++ domainDepsIn(idx)
      case ast.SeqTake(s, n) => domainDepsIn(s) ++ domainDepsIn(n)
      case ast.SeqDrop(s, n) => domainDepsIn(s) ++ domainDepsIn(n)
      case ast.SeqContains(elem, s) => domainDepsIn(elem) ++ domainDepsIn(s)
      case ast.SeqUpdate(s, idx, elem) => domainDepsIn(s) ++ domainDepsIn(idx) ++ domainDepsIn(elem)
      case ast.SeqLength(s) => domainDepsIn(s)

      case _: ast.EmptySet => DomainDeps.empty
      case ast.AnySetContains(elem, s) => domainDepsIn(elem) ++ domainDepsIn(s)
    }
  }

  private val pureFunctions: Seq[ast.Function] = obl.s.program.functions.filter(f => f.isPure)
  val domains: Seq[(Domain, DomainDeps)] = obl.s.program.domains.filter(
    d => !d.name.endsWith("WellFoundedOrder")).map(
    d => (d, getDomainDeps(d)))

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
  private lazy val renaming: immutable.Map[state.Identifier, String] = {
    val varMap = mutable.Map[state.Identifier, String]()
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
    if (de.description.contains("Loop invariant")) {
      strings += "  (* Begin loop invariant *)"
      for (child <- de.children) {
        translateDebugExp(child)
      }
      strings += "  (* End loop invariant *)"
    } else if (de.description.contains("Joined path conditions")) {
      for (child <- de.children) {
        translateDebugExp(child)
      }
      // } else if (de.description.contains("precondition of")) {
      // Do nothing
    } else {
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
          if (de.term.isDefined) {
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

  def varHead(name: String): String = name.split('@')(0)
  def idHead(id: state.Identifier): String = varHead(id.name)

  // Removes special Isabelle chars
  def safeId(id: state.Identifier): String = {
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

  def matches(lVar: ast.AbstractLocalVar, id: state.Identifier): Boolean = {
    idHead(id) == lVar.name
  }

  // Used to determine if wrapping brackets are needed
  def isSingleTokenTerm(term: terms.Term): Boolean = {
    term match {
      case _: terms.Var => true
      case _: terms.IntLiteral => true
      case _: terms.BooleanLiteral => true
      case _: terms.Not => true
      case _: terms.SeqNil => true
      case _: terms.SeqSingleton => true
      case _: terms.EmptySet => true
      case _: terms.SingletonSet => true
      case _: terms.EmptyMultiset => true
      case _: terms.EmptyMap => true
      case terms.NoPerm => true
      case terms.FullPerm => true
      case _ => false
    }
  }

  def isSingleTokenExp(e: ast.Exp): Boolean = {
    e match {
      case _: ast.IntLit => true
      case _: ast.TrueLit => true
      case _: ast.FalseLit => true
      case _: ast.NullLit => true
      case _: ast.LocalVar => true
      case _: ast.FieldAccess => true
      case ast.FuncApp(_, args) => args.isEmpty
      case ast.DomainFuncApp(_, args, _) => args.isEmpty
      case _: ast.Not => true
      case _: ast.EmptySeq => true
      case _: ast.ExplicitSeq => true
      case _: ast.EmptySet => true
      case _: ast.EmptyMultiset => true
      case _: ast.EmptyMap => true
      case _ => false
    }
  }

  def notSnap(term: terms.Term): Boolean = {
    term match {
      case terms.BuiltinEquals(_, snap) => snap.sort != terms.sorts.Snap
      case _ => true
    }
  }

  def quantifierToString(q: terms.Quantifier): String = {
    q match {
      case terms.Forall => "\\<forall>"
      case terms.Exists => "\\<exists>"
    }
  }

  def validName(name: String): Boolean = {
    val isabelleKeywords = Seq("value")
    !isabelleKeywords.contains(name)
  }
}