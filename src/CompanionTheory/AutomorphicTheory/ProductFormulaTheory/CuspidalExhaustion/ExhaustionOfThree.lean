module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.CuspEmbP
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.ExhaustionOfSteps
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.IrreducibleAdmissibleGL
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.IsLAddSegmentOfInjectiveOfNotPrecedes
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.JuxtPOfFineUniq
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.NotAboveTransGenSelf
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.SquareIntegrableSegments.SegmentReordering.CsOrderfree
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosocleOfContragredientSocleStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubSegmentProductStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsExhaustionGlStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsFactorsDualReverseOrderedStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSegmentDualStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFreeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLanglandsOfIrreducibleAdmissibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLengthStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReverseOrderedProductHasSocleStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetAllStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentProductWordInShuffleStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducibleStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace CompanionTheory.Exh

variable (hZ : GlobalTheory.Published.SegmentRepresentation) (hI : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZSeg.LUnlinkedIrr k)

include hZ hI in
theorem standardCosocle_of : GlobalTheory.Published.StandardCosocleGL := by
  have hA := irreducibleAdmissibleGL
  intro k _ _ _ _ _ 𝔪 h N x hd hx
  obtain ⟨Γ, hΓ, hL⟩ := GlobalTheory.T.langlands_factors_dual_reverse_ordered hA (GlobalTheory.T.langlands_segment_dual hA hZ) 𝔪 x hx
  obtain ⟨hd', ⟨e⟩⟩ := GlobalTheory.T.contragredient_product_irreducible hA x hd
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.reverse_ordered_product_has_socle hA (GlobalTheory.T.segment_jacquet_all hA hZ) (hI k) (GlobalTheory.T.unlinked_commute_of_irreducible k hA (hI k)) Γ (fun a => dualCl (x a)) hd' hΓ hL
  exact GlobalTheory.T.cosocle_of_contragredient_socle hA (prodIrr x hd) (isSmooth_prodIrr x hd) (GlobalTheory.T.product_irreducible_finite_length hA x hd) τ
    (hτ.of_equiv (Representation.Equiv.refl _) e.symm)

include hI in
theorem lOrderFree_of (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : LOrderFree k :=
  CompanionTheory.PfEss.Zc2.cs_orderfree irreducibleAdmissibleGL (GlobalTheory.T.unlinked_commute_of_irreducible k irreducibleAdmissibleGL (hI k))

include hI in
theorem lSocleGL_of (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : LSocleGL k :=
  GlobalTheory.T.langlands_socle_of_order_free irreducibleAdmissibleGL (GlobalTheory.T.local_langlands_of_irreducible_admissible irreducibleAdmissibleGL) (lOrderFree_of hI k)

include hZ hI in
theorem exhaustion_of_three (H : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], MidP k ∧ RefineP k ∧ SwapP k) : GlobalTheory.Published.LanglandsExhaustionGL := by
  have hA := irreducibleAdmissibleGL
  refine exhaustion_of_steps fun k _ _ _ _ _ => ?_
  obtain ⟨hM, hR, hS⟩ := H k
  have hC := cuspEmbP_of_refine k hR
  exact ⟨hM, hR, hS, hC, suppP k, juxtP_of_fineUniq hA hM hR hS hC (GlobalTheory.T.segment_product_word_in_shuffle hA (GlobalTheory.T.segment_jacquet_all hA hZ)) (GlobalTheory.T.irreducible_sub_segment_product hA hZ),
    linkP, minP, peelGoodP (standardCosocle_of hZ hI) (lSocleGL_of hI k) hR⟩

include hZ hI in
theorem multisegments_of (hE : GlobalTheory.Published.LanglandsExhaustionGL) : GlobalTheory.Published.LanglandsMultisegments :=
  GlobalTheory.T.langlands_multisegments_of_exhaustion_gl irreducibleAdmissibleGL (lSocleGL_of hI) (fun _ _ _ _ _ => GlobalTheory.T.segment_jacquet_all irreducibleAdmissibleGL hZ) (lOrderFree_of hI) hE

end CompanionTheory.Exh

end
