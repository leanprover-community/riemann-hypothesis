module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FGLeaf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsNormalisedOfDualIsConj
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.SaturationTransportPair
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatGLOfInvT

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FG

open JetMatrixAlgebra GlobalTheory.ThetaSatake in
theorem conjFix_holds : ConjFix := by
  intro E _ _ _ a b
  refine ⟨fun w u G _ hwu hG => ?_, fun S hS => ⟨fun u hu => ?_, fun X => ?_⟩⟩
  · obtain ⟨x, rfl⟩ : ∃ x, cw x = w := ⟨cw w, GlobalTheory.ThetaPull.conjSrc_conjSrc w⟩
    obtain rfl : u = x := (GlobalTheory.CompanionTheory.OneExDatum.eq_cw_of_conjPl hwu).trans (GlobalTheory.ThetaPull.conjSrc_conjSrc x)
    rw [pairRtT_cw] at hG
    refine (mem_fixed_comp_symm _ (fun g => ?_)).1 hG
    show g ∈ (KGL u (n := a)).prod (KGL u (n := b)) ↔ ((fx u a).prodCongr (fx u b)) g ∈ (KGL (cw u) (n := a)).prod (KGL (cw u) (n := b))
    rw [Subgroup.mem_prod, Subgroup.mem_prod]
    exact and_congr (mem_fx_iff u a g.1) (mem_fx_iff u b g.2)
  · obtain ⟨w, ⟨hwS, hwu⟩, -⟩ := hS u
    by_cases h : w = u
    · exact Or.inl (h ▸ hwS)
    · exact Or.inr ⟨w, hwS, ⟨u, Ne.symm h, hwu.symm⟩, hwu.symm, Or.inl (Ne.symm h)⟩
  · refine (X.finite_toSet.image cw).subset fun u hu => ?_
    obtain ⟨w, hw, hwu⟩ := hu
    exact ⟨w, hw, (GlobalTheory.CompanionTheory.OneExDatum.eq_cw_of_conjPl hwu).symm⟩

end PositivityTheory.Rg.BcB.F.FG

end
