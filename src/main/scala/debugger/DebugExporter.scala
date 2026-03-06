package viper.silicon.debugger

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.debugger.ExportUtils._
import viper.silicon.debugger.Rewrites.{addRename, addRenames}
import viper.silicon.state
import viper.silicon.state.{Identifier, terms}
import viper.silicon.state.terms.Term
import viper.silicon.resources
import viper.silicon.resources.{FieldID, PredicateID}
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

// Old type, should delete
case class ReplacementTriple(exp: ast.Exp, condition: Option[ast.Exp], fun: ast.Function)

// Things to rewrite as you translate terms
case class Rewrites(varRenames: immutable.Map[state.Identifier, String],
                    termReplacements: immutable.Map[ast.Exp, ReplacementTriple])

object Rewrites {
  def apply(varRenames: immutable.Map[state.Identifier, String],
            termReplacements: immutable.Map[ast.Exp, ReplacementTriple]): Rewrites = {
    new Rewrites(varRenames, termReplacements)
  }

  def addRename(rewrites: Rewrites, id: Identifier, rep: String): Rewrites = {
    Rewrites(rewrites.varRenames + (id -> rep), rewrites.termReplacements)
  }

  def addRenames(rewrites: Rewrites, toAdd: Map[Identifier, String]): Rewrites = {
    Rewrites(rewrites.varRenames ++ toAdd, rewrites.termReplacements)
  }
}

/**
 * Translates Silver expressions and Silicon terms into Isabelle syntax.
 * Takes abstraction maps and renamings to change the translation.
 */
class Translator(val obl: ProofObligation, val filename: String) {
  var strings = ArrayBuffer[String]() // Strings to be written to .thy file
  private lazy val basicRewrites: Rewrites = Rewrites(renaming2, immutable.Map())

  def translateObligation(): Unit = {
    strings += s"theory $filename\n"
    strings += "imports \"~/Viper/isabelle/ViperTranslations\"\n"
    strings += "begin\n\n"

    declareDomainTypes()
    defineFields()
    translateDomainsAndFunctions()
    abbreviateFields()
    generateLemma()

    strings += "end"
  }

  private def declareDomainTypes(): Unit = {
    // First declare domain types
    if (domains.nonEmpty) {
      strings += "text \\<open>Declare domain types\\<close>\n"
      domains.foreach(d => strings += "typedecl " + d._1.name)
      strings += ""
    }
  }

  private def defineFields(): Unit = {
    if (obl.s.program.fields.isEmpty) return

    strings += "text \\<open>Define fields and heap\\<close>\n"
    strings += "record Object ="
    obl.s.program.fields.foreach(fld => strings += s"  ${fld.name}_' :: \"${translateType(fld.typ)}\"")
    strings += "\ntype_synonym Heap = \"ref \\<Rightarrow> Object\"\n"
  }

  private def translateDomainsAndFunctions(): Unit = {
    strings += "text \\<open>Translated domains and functions\\<close>\n"
    val (independentDomains, dependentDomains) = domains.partition(domDeps => DomainDeps.isSelfContained(domDeps._1))

    def functionType(fn: FuncLike, isPrecondition: Boolean = false, isHeapDep: Boolean = false): String = {
      val name = if (isPrecondition) fn.name + "_pre" else fn.name
      val maybeHeap = if (isHeapDep) " Heap \\<Rightarrow> " else ""
      val argString = fn.formalArgs.map(a => translateType(a.typ) + " \\<Rightarrow> ").mkString("")
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

    // Create combined locale
    strings += "locale All_Functions = Program_Functions +"
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
    obl.s.program.functions.foreach(translateFunctionDefs)
    strings += ""
  }

  private def translateFunctionDefs(fn: ast.Function): Unit = {
    val argString = (if (fn.isPure) "" else "h ") + fn.formalArgs.map(_.name).mkString(" ")

    // Translate function body
    if (fn.body.isDefined) {
      val fnRHS = fn.body.get match {
        case _: ast.Not => "(" + translateExp(fn.body.get) + ")"
        case _ => translateExp(fn.body.get)
      }
      if (fn.pres.isEmpty) {
        strings += s"  assumes ${fn.name}_def: \"\\<And>$argString. ${fn.name} $argString =\n    $fnRHS\""
      } else {
        strings += s"  assumes ${fn.name}_def: \"\\<And>$argString. " +
          s"${fn.name}_pre $argString \\<Longrightarrow> ${fn.name} $argString =\n    $fnRHS\""
      }
      // Translate internal function calls
      extractPropagation(fn.name) match {
        case None =>
        case Some((vars, body)) =>
          var newRenames = vars.tail.map(v => (v.id, v.id.name.takeWhile(_ != '@'))).toMap
          if (!fn.isPure) newRenames = newRenames + (vars.head.id -> "h")
          val newRewrites = addRenames(basicRewrites, newRenames)
          def translate: Term => String = translateTerm(_, newRewrites, options = defaultOptions.collapseSnapsOn())

          val bodyString = body match {
            case terms.Implies(p0, p1) => translate(p0) + " \\<Longrightarrow> " + translate(p1)
            case _ => translate(body)
          }
          //val propString = translateTerm(prop, newRewrites, collapseSnaps = true).replace("NO_HEAP", "h")
          // TODO: use argString and fix variables with unnecessary suffixes
          strings += s"  assumes ${fn.name}_calls: \"\\<And>$argString. ${bodyString.replace("NO_HEAP", "h")}\""
      }
    }
    // TODO: Translate function postconditions???
    // Framing axioms, currently only added if no function body
    if (!fn.isPure && fn.body.isEmpty) {
      val argStringH1 = "h1" + argString.drop(1)
      val argStringH2 = "h2" + argString.drop(1)
      val footprint = fn.pres.filter(!_.isPure).map(translateExp(_, isFrameAxiom = true)).mkString(" \\<and> ")
      strings += s"  assumes ${fn.name}_framing: \"\\<And>h1 $argStringH2. " +
        s"${fn.name}_pre $argString \\<and> ${fn.name}_pre $argStringH2"
      strings += s"    \\<and> $footprint"
      strings += s"    \\<Longrightarrow> ${fn.name} $argStringH1 = ${fn.name} $argStringH2\""
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



  private def abbreviateFields(): Unit = {
    strings += "text \\<open>Simpler field notation for the current heap\\<close>\n"
    strings += "locale Program = All_Functions +"
    if (obl.s.program.fields.isEmpty) {
      strings += "  assumes True (* no functions to translate *)\n"
      return
    }

    for (h <- obl.s.oldHeaps) {
      strings += s"  fixes ${safeString(h._1)} :: Heap"
    }
    strings += "  fixes curr :: Heap"
    strings += "\ncontext Program\nbegin\n"
    for (f <- obl.s.program.fields) {
      strings += s"abbreviation ${f.name} :: \"ref \\<Rightarrow> ${translateType(f.typ)}\" where"
      strings += s"  \"${f.name} r \\<equiv> ${f.name}_' (curr r)\"\n"
    }
    strings += "end\n"
  }

  private def generateLemma(): Unit = {
    strings += "text \\<open>Proof obligation\\<close>\n"
    strings += "context Program\nbegin\n\nlemma"
    translateStore()
    translateHeaps()
    strings += "  (* Assumptions *)"
    obl.assumptionsExp.foreach(translateDebugExp)

    strings += "  shows \"" + translateTerm(obl.assertion) + "\""
    strings += "  (* Complete proof here *)\n  sorry\n"
    strings += "end\n"
  }

  private def translateStore(): Unit = {
    strings += "  (* Local variables *)"
    for ((v, (t, e)) <- obl.s.g.values) {
      if (e.isDefined) {
        val typeStr = if (heapMap contains t.toString) {
          heapMap(t.toString).toString().replace("__Abst","")
        } else {
          translateType(e.get.typ) }
        strings += s"  fixes ${safeString(v.name)} :: \"$typeStr\""
      }
    }
  }

  private def translateHeaps(): Unit = {
    translateHeap(obl.s.h, "curr")
    obl.s.oldHeaps.foreach { case (label, heap) => translateHeap(heap, label) }
  }

  private def translateHeap(h: state.Heap, label: String): Unit = {
    if (label == "curr")
      strings += "  (* Current heap *)"
    else
      strings += s"  (* Heap $label *)"
    for ((c, idx) <- h.values.zipWithIndex) {
      c match {
        case bc: state.BasicChunk =>
          bc.resourceID match {
            case FieldID =>
              if (bc.args.length == 1) {
                val ref = translateTerm(bc.args.head)
                val permCondition = permCondSimp(bc.perm)
                val field = if (label == "curr") s"${bc.id.name} $ref" else s"${bc.id.name}_' (${safeString(label)} r)"
                val chunk = translateTerm(permCondition) + s" \\<Longrightarrow> $field = ${translateTerm(bc.snap)}"
                strings += s"  assumes ${safeString(label)}_$idx: \"$chunk\""
              } else {
                strings += s"  (* Error: $bc has wrong args *)"
              }
            case PredicateID =>
          }
        case qfc: state.QuantifiedFieldChunk =>
          val permCondition = terms.And(qfc.condition, permCondSimp(qfc.permValue))
          val field = if (label == "curr") s"${qfc.id.name} r" else s"${qfc.id.name}_' (${safeString(label)} r)"
          val chunk = "\\<And>r. " + translateTerm(permCondition) + " \\<Longrightarrow> " +
            s"$field = ${qfc.id}_${translateTerm(qfc.fvf)} r"
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
                            rewrites: Rewrites = basicRewrites,
                            options: TranslationOptions = defaultOptions): String = {
    // Recursive call, for convenience
    def rec(term2: Term): String = translateTerm(term2, rewrites, options)
    def maybeBracket(term2: terms.Term, options2: TranslationOptions = options): String =
      if (isSingleTokenTerm(term2))
        translateTerm(term2, rewrites, options2)
      else "(" + translateTerm(term2, rewrites, options2) + ")"

    term match {
      // Functions and Applications
      case terms.Var(id, _, _) => rewrites.varRenames getOrElse(id, safeId(id))
      case terms.Let(bindings, body) =>
        val bindString = bindings.transform((bVar, bTerm) => rec(bVar) + " = " + rec(bTerm)).mkString("; ")
        s"let $bindString in ${rec(body)}"
      case terms.Null => "Null"
      case terms.Unit => "UNIT"
      case terms.App(applicable, args, heapLabel) =>
        val og_fn = applicable.id.name.takeWhile(_ != '%')
        obl.s.program.findFunctionOptionally(og_fn) match {
          case None => safeId(applicable.id) + args.map(" " + maybeBracket(_)).mkString("")
          case Some(f) => if (f.isPure) s"${safeId(applicable.id)}" + args.tail.map(" " + maybeBracket(_)).mkString("")
            else s"${safeId(applicable.id)} ${safeString(heapLabel.getOrElse("NO_HEAP"))} " + args.tail.map(maybeBracket(_)).mkString(" ")
        }
      // Stuff
      case terms.IntLiteral(i) => if (options.annotateIntLits) s"($i::int)" else i.toString()
      case b: terms.BooleanLiteral => b.toString
      case terms.Quantification(q, vars, body, _, _, _, _) => quantifierToString(q) +
        vars.map(v =>
          if (rewrites.varRenames.contains(v.id)) rewrites.varRenames(v.id)
          else safeId(v.id)).mkString(" ") + ". " + rec(body)
      // Arithmetic
      case terms.Plus(left, right) => rec(left) + " + " + rec(right)
      case terms.Minus(left, right) => rec(left) + " - " + rec(right)
      case terms.Times(left, right) => rec(left) + " * " + rec(right)
      case terms.Div(left, right) => "(" + rec(left) + " div " + rec(right) + ")"
      case terms.Mod(left, right) => rec(left) + " mod " + rec(right)
      // Logic
      case terms.Not(t) => "\\<not>" + maybeBracket(t)
      case terms.Or(subterms) => subterms.map(maybeBracket(_)).mkString(" \\<or> ") //seqOpToString(subterms, "\\<or>")
      case terms.And(subterms) => subterms.map(maybeBracket(_)).mkString(" \\<and> ")
      case terms.Implies(left, right) =>
        maybeBracket(left) + " \\<longrightarrow> " + maybeBracket(right)
      case terms.Iff(left, right) =>
        rec(left) + " \\<longleftrightarrow> " + rec(right)
      case terms.Ite(cond, tThen, tElse) => s"if ${maybeBracket(cond)} then ${maybeBracket(tThen)} else ${maybeBracket(tElse)}"
      case terms.BuiltinEquals(left, right) => maybeBracket(left) + " = " + maybeBracket(right)
      case terms.CustomEquals(left, right) => maybeBracket(left) + " = " + maybeBracket(right)
      //Comparison
      case terms.Less(left, right) => rec(left) + " < " + rec(right)
      case terms.AtMost(left, right) => rec(left) + " \\<le> " + rec(right)
      case terms.Greater(left, right) => rec(left) + " > " + rec(right)
      case terms.AtLeast(left, right) => rec(left) + " \\<ge> " + rec(right)
      // Permissions
      case terms.NoPerm => "(0::perm)"
      case terms.FullPerm => "(1::perm)"
      case terms.FractionPermLiteral(r) => r.toString
      case terms.PermTimes(p0, p1) => s"${maybeBracket(p0)} * ${maybeBracket(p1)}"
      case terms.IntPermTimes(p0, p1) => s"${maybeBracket(p0)} * ${maybeBracket(p1, options.annotateIntLitsOff())}"
      case terms.PermIntDiv(p0, p1) => s"${maybeBracket(p0)} / ${maybeBracket(p1, options.annotateIntLitsOff())}"
      case terms.PermPermDiv(p0, p1) => s"${maybeBracket(p0)} / ${maybeBracket(p1)}"
      case terms.PermPlus(p0, p1) => s"${maybeBracket(p0)} + ${maybeBracket(p1)}"
      case terms.PermMinus(p0, p1) => s"${maybeBracket(p0)} - ${maybeBracket(p1)}"
      case terms.PermLess(p0, p1) => s"${maybeBracket(p0)} < ${maybeBracket(p1)}"
      case terms.PermMin(p0, p1) => s"min ${maybeBracket(p0)} ${maybeBracket(p1)}"
      // Sequences
      case terms.SeqRanged(from, to) => "[" + rec(from) + ".." + rec(to) + "]"
      case terms.SeqNil(_) => "[]" // Note: not using sort, maybe add type annotation
      case terms.SeqSingleton(elem) => "[" + rec(elem) + "]"
      case terms.SeqAppend(left, right) => rec(left) + "@" + rec(right)
      case terms.SeqDrop(seq, n) => "drop\\<^sub>Z " + maybeBracket(n) + " " + maybeBracket(seq)
      case terms.SeqTake(seq, n) => "take\\<^sub>Z " + maybeBracket(n) + " " + maybeBracket(seq)
      case terms.SeqLength(seq) => "length\\<^sub>Z " + maybeBracket(seq)
      case terms.SeqAt(seq, idx) => maybeBracket(seq) + "!\\<^sub>Z" + maybeBracket(idx)
      case terms.SeqIn(seq, elem) => rec(elem) + " \\<in>: " + rec(seq)
      case terms.SeqInTrigger(_, _) => "error: SeqInTrigger"
      case terms.SeqUpdate(seq, idx, value) => s"list_update ${rec(seq)} ${rec(idx)} ${rec(value)}"
      // Sets
      case terms.EmptySet(_) => "{}\\<^sup>+"
      case terms.SingletonSet(elem) => s"{${rec(elem)}}\\<^sup>+"
      case terms.SetAdd(left, right) => "insert_fin " + maybeBracket(right) + " " + maybeBracket(left)
      case terms.SetUnion(left, right) => rec(left) + " \\<union>\\<^sup>+ " + rec(right)
      case terms.SetIntersection(left, right) => rec(left) + " \\<inter>\\<^sup>+ " + rec(right)
      case terms.SetSubset(left, right) => rec(left) + " \\<subset>\\<^sup>+ " + rec(right)
      case terms.SetDisjoint(left, right) => "disjnt_finset " + maybeBracket(left) + " " + maybeBracket(right)
      case terms.SetDifference(left, right) => rec(left) + " \\<setminus>\\<^sup>+ " + rec(right)
      case terms.SetIn(elem, set) => rec(elem) + " \\<in>\\<^sup>+ " + maybeBracket(set)
      case terms.SetCardinality(set) => "card\\<^sub>Z " + maybeBracket(set)
      // Multisets
      case terms.EmptyMultiset(_) => "{#}"
      case terms.SingletonMultiset(elem) => "{#" + rec(elem) + "#}"
      case terms.MultisetAdd(_, _) => "error multiset add"
      case terms.MultisetUnion(left, right) => rec(left) + " + " + rec(right)
      case terms.MultisetCardinality(mset) => "size\\<^sub>Z " + maybeBracket(mset)
      case terms.MultisetCount(mset, elem) => "count\\<^sub>Z " + maybeBracket(mset) + " " + maybeBracket(elem)
      // Maps
      case terms.EmptyMap(_, _) => "Map.empty"
      case terms.MapLookup(base, key) => maybeBracket(base) + "@@" + maybeBracket(key)
      case terms.MapCardinality(map) => "card\\<^sub>Z (dom " + maybeBracket(map) + ")"
      case terms.MapUpdate(map, key, value) => maybeBracket(map) + "(" + rec(key) + "\\<mapsto>" + rec(value) + ")"
      case terms.MapDomain(map) => "dom " + maybeBracket(map)
      case terms.MapRange(map) => "ran " + maybeBracket(map)
      // Snapshots
      case terms.Combine(_, _) => "undefined"
      case terms.First(snap) => if (options.collapseSnaps) rec(snap) else "F" + rec(snap)
      case terms.Second(snap) => if (options.collapseSnaps) rec(snap) else "S" + rec(snap)
      // Quantified Permissions
      case terms.Lookup(field, fvf, at) =>
        if (options.collapseSnaps) s"$field (${rec(fvf)} ${maybeBracket(at)})"
        else s"${field}_${rec(fvf)} ${maybeBracket(at)}"
      case terms.PermLookup(field, pm, at) => "undefined"
      case terms.Domain(field, fvf) => s"(fvf_domain ${field}_${rec(fvf)})"
      case terms.HasDomain(field, fvf, _) => s"(has_domain ${field}_${rec(fvf)})"
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
      case terms.SortWrapper(t, _) => rec(t)
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

  def translateFunType(fn: ast.FuncLike): String = {
    "" // TODO
  }

  private def setPostfix(t: ast.Type): String = {
    t match {
      case _: ast.SetType => "\\<^sup>+"
      case _: ast.MultisetType => "#"
    }
  }

  private def translateExp(e: ast.Exp, isFrameAxiom: Boolean = false): String = {
    def rec(e2: ast.Exp): String = translateExp(e2, isFrameAxiom)
    def maybeBracket(e2: ast.Exp): String = if (isSingleTokenExp(e2)) rec(e2) else "(" + rec(e2) + ")"

    e match {
      case ast.Add(left, right) => rec(left) + " + " + rec(right)
      case ast.Sub(left, right) => rec(left) + " - " + rec(right)
      case ast.Mul(left, right) => rec(left) + " * " + rec(right)
      case ast.Div(left, right) => rec(left) + " / " + rec(right)
      case ast.Mod(left, right) => rec(left) + " % " + rec(right)
      case ast.LtCmp(left, right) => rec(left) + " < " + rec(right)
      case ast.LeCmp(left, right) => rec(left) + " \\<le> " + rec(right)
      case ast.GtCmp(left, right) => rec(left) + " > " + rec(right)
      case ast.GeCmp(left, right) => rec(left) + " \\<ge> " + rec(right)
      case ast.EqCmp(left, right) => rec(left) + " = " + rec(right)
      case ast.NeCmp(left, right) => rec(left) + " \\<noteq> " + rec(right)

      case ast.IntLit(i) => i.toString()
      case ast.Minus(exp) => "(-" + rec(exp) + ")"
      case ast.Or(left, right) => rec(left) + " \\<or> " + rec(right)
      case ast.And(left, right) =>
        if (isFrameAxiom && left.isPure) rec(right)
        else if (isFrameAxiom && right.isPure) rec(left)
        else rec(left) + " \\<and> " + rec(right)
      case ast.Implies(left, right) => translateExp(left) + " \\<longrightarrow> " + rec(right)
      case ast.MagicWand(left, right) => rec(left) + " \\<longrightarrow> " + rec(right)
      case ast.Not(exp) => "\\<not>(" + rec(exp) + ")"
      case ast.TrueLit() => "True"
      case ast.FalseLit() => "False"
      case ast.NullLit() => "Null"
      case ast.FieldAccessPredicate(loc, _) =>
        if (isFrameAxiom) s"${loc.field.name}_' (h1 ${maybeBracket(loc.rcv)}) = ${loc.field.name}_' (h2 ${maybeBracket(loc.rcv)})"
        else "undefined"

      case ast.FuncApp(funcname, args) =>
        // Add implicit heap argument for heap-dep functions
        val maybeHeap = if (obl.s.program.findFunction(funcname).isPure) "" else " h"
        funcname + maybeHeap + args.map(a => " " + maybeBracket(a)).mkString("")
      case ast.DomainFuncApp(funcname, args, _) => funcname + " " + args.map(maybeBracket).mkString(" ")
      case ast.FieldAccess(rcv, field) => s"(${field.name}_' (h ${maybeBracket(rcv)}))"

      case ast.CondExp(cond, thn, els) => "(if " + rec(cond) + " then " + rec(thn) +
        " else " + rec(els) + ")"
      case ast.Asserting(_, body) => rec(body)
      case ast.Let(variable, exp, body) =>
        s"let ${safeString(variable.name)} = ${rec(exp)} in ${rec(body)}"
      case ast.Forall(variables, _, exp) =>
        "(\\<forall>" + variables.map(v => safeString(v.name)).mkString(" ") + ". " + rec(exp) + ")"
      case ast.Exists(variables, _, exp) =>
        "(\\<exists>" + variables.map(v => safeString(v.name)).mkString(" ") + ". " + translateExp(exp) + ")"
      case ast.LocalVar(name, _) => safeString(name)
      case ast.Result(_) => "result" // TODO: this is currently meaningless
      case ast.LocalVarWithVersion(name, _) => safeString(name)

      case ast.EmptySeq(_) => "[]"
      case ast.ExplicitSeq(elems) => "[" + elems.map(rec).mkString(", ") + "]"
      case ast.RangeSeq(low, high) => s"[${rec(low)}..${rec(high)}]"
      case ast.SeqAppend(left, right) => rec(left) + " @ " + rec(right)
      case ast.SeqIndex(s, idx) => s"${maybeBracket(s)} !\\<^sub>Z ${maybeBracket(idx)}"
      case ast.SeqTake(s, n) => "take\\<^sub>Z " + maybeBracket(n) + " " + maybeBracket(s)
      case ast.SeqDrop(s, n) => "drop\\<^sub>Z " + maybeBracket(n) + " " + maybeBracket(s)
      case ast.SeqContains(elem, s) => rec(elem) + " \\<in>: " + rec(s)
      case ast.SeqUpdate(s, idx, elem) => s"list_update ${maybeBracket(s)} ${maybeBracket(idx)} ${maybeBracket(elem)}"
      case ast.SeqLength(s) => "length\\<^sub>Z " + maybeBracket(s)

      case ast.EmptySet(_) => "{}\\<^sup>+"
      case ast.ExplicitSet(elems) => "{" + elems.map(rec).mkString(", ") + "}\\<^sup>+"
      case ast.EmptyMultiset(_) => "{#}"
      case ast.ExplicitMultiset(elems) => "{#" + elems.map(rec).mkString(", ") + "#}"
      case ast.AnySetUnion(left, right) =>
        maybeBracket(left) + s" \\<union>${setPostfix(left.typ)} " + maybeBracket(right)
      case ast.AnySetIntersection(left, right) =>
        maybeBracket(left) + s" \\<inter>${setPostfix(left.typ)} " + maybeBracket(right)
      case ast.AnySetSubset(left, right) =>
        maybeBracket(left) + s" \\<subset>${setPostfix(left.typ)} " + maybeBracket(right)
      case ast.AnySetMinus(left, right) =>
        maybeBracket(left) + " - " + maybeBracket(right)
      case ast.AnySetContains(elem, s) =>
        maybeBracket(elem) + s" \\<in>${setPostfix(s.typ)} " + maybeBracket(s)
      case ast.AnySetCardinality(s) =>
        s.typ match {
          case _: ast.SetType => "card\\<^sub>Z"
          case _: ast.MultisetType => "size\\<^sub>Z"
        }

      case ast.EmptyMap(_, _) => "empty_finmap"
      case ast.ExplicitMap(elems) => "" //TODO
      case ast.Maplet(key, value) => s"[${rec(key)}\\<mapsto>${rec(value)}]\\<^sup>+"
      case ast.MapUpdate(base, key, value) => "" // TODO
      case ast.MapContains(key, base) => maybeBracket(key) + " \\<in>m " + maybeBracket(base)
      case ast.MapCardinality(base) => "finmap_card " + maybeBracket(base)
      case ast.MapDomain(base) => "dom_finmap " + maybeBracket(base)
      case ast.MapRange(base) => "ran_finmap " + maybeBracket(base)

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

  private def termMatchInReplacements(term: terms.Term, reps: Rewrites): Option[ReplacementTriple] = {
    /*term match {
      case _: terms.SetIn =>
        println(term.toString)
        reps.termReplacements.foreach(x => println(x._1))
      case _ =>
    }*/
    for ((k, v) <- reps.termReplacements) {
      if (termExpMatch(term, k)) {
        return Some(v)
      }
    }
    None
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

  // Rename variables (only, not Snaps) based on store and heap
  private val renaming2: immutable.Map[state.Identifier, String] = {
    val renaming = mutable.Map[state.Identifier, String]()
    // Add local vars from the store
    for ((lVar, term) <- obl.s.g.termValues) {
      term match {
        case terms.Var(id, _, _) =>
      if (!(renaming contains id)) {
      renaming += id -> safeString(lVar.toString) // add if non-existent
      } else if (idHead(id) == lVar.name) {
        renaming(id) = safeString(lVar.toString) // update if better match found
      }
        case _ => ()
      }
    }
    // Add location variables from the heap
    for (chunk <- obl.s.h.values) {
      chunk match {
        case bc: state.BasicChunk =>
          bc.resourceID match {
            // If the chunk is a basic field access, add renaming
            case resources.FieldID =>
              (bc.args.head, bc.snap) match {
                case (v: terms.Var, s: terms.Var) =>
                  renaming += s.id -> (renaming.getOrElse(v.id, safeId(v.id)) + "_" + bc.id.name)
                case _ => println("FieldID doesn't match: " + bc.snap + bc.args)
              }
            case _ => ()
          }
        case _ =>
      }
    }
    renaming.toMap
  }

  // Map recording all predicates in the heap
  private val heapMap: immutable.Map[String, ast.Type] = {
    val tempMap = mutable.Map[String, ast.Type]()
/*    for (chunk <- obl.s.h.values) {
      chunk match {
        case c: state.BasicChunk =>
          c.resourceID match {
            case viper.silicon.resources.PredicateID =>
              if (abstractionMap contains c.id.name) {
                println("Testings args in processHeap()")
                c.args.head match {
                  case terms.Var(id, _, _) => tempMap(id.name) = abstractionMap(c.id.name)._1
                }
                // heapMap(c.args.head) = abstractionMap(c.id.name)._1
              }
            case _ =>
          }
      }
    }*/
    tempMap.toMap
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

    /* OLD VERSION WITH SORTING
    val idGroups = (freeVars.map(v => v.id) -- varMap.keys).groupBy(id => id.toString.split('@')(0))

    def orderId(id1: Identifier, id2: Identifier): Boolean = {
      id1.name.split('@')(1).toInt > id2.name.split('@')(1).toInt
    }

    for ((prefix, list) <- idGroups) {
      val ordered = list.toArray.sortWith(orderId)
      val newVars = ordered.zipWithIndex.map { case (id, n) => safeString(prefix) + s"_$n" }
      varMap ++= ordered.zip(newVars)
    }*/
    varMap.toMap
  }

  private def translateDebugExp(de: DebugExp): Unit = {
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
    } else if (de.description.contains("precondition of")) {
      // Do nothing
    } else if (de.term.isDefined) {
      if (notSnap(de.term.get)) {
        //val varTerm = filterPure(variablise(de.term.get))
        val varTerm = filterPure(de.term.get)
        val pureTerm = filterPure(de.term.get)
        if (pureTerm.isDefined) {
          strings += "  assumes " + de.id + ": \"" + translateTerm(varTerm.get) + "\""
        }
      }
    }
  }

}

// Things that will never be dependent on the particular program
object ExportUtils {
  def permCondSimp(p: Term): Term = {
    booleanSimp(isPosSimp(collapseITE(p)))
  }

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
}