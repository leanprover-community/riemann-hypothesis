module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.EmbeddingMiddleFactorTriple
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.ExhaustionOfThree
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.IrreducibleAdmissibleGL
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.LUnlinkedIrrOfSeg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducibleStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace CompanionTheory.Exh

theorem standardCosocleGL_of_seg (hZ : GlobalTheory.Published.SegmentRepresentation) : GlobalTheory.Published.StandardCosocleGL :=
  standardCosocle_of hZ (lUnlinkedIrr_of_seg hZ)

theorem langlandsExhaustionGL_of_seg (hZ : GlobalTheory.Published.SegmentRepresentation) : GlobalTheory.Published.LanglandsExhaustionGL :=
  exhaustion_of_three hZ (lUnlinkedIrr_of_seg hZ) fun k _ _ _ _ =>
    ⟨midP' k irreducibleAdmissibleGL, refineP' k,
      swapP' k (GlobalTheory.T.unlinked_commute_of_irreducible k irreducibleAdmissibleGL (lUnlinkedIrr_of_seg hZ k))⟩

theorem langlandsMultisegments_of_seg (hZ : GlobalTheory.Published.SegmentRepresentation) : GlobalTheory.Published.LanglandsMultisegments :=
  multisegments_of hZ (lUnlinkedIrr_of_seg hZ) (langlandsExhaustionGL_of_seg hZ)

end CompanionTheory.Exh
