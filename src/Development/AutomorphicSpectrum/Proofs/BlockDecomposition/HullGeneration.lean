module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

theorem typeB_of_mem_span {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    {K : Subgroup (GL (Fin N) (Af E))} {W : Submodule ℂ (Kinf E N → ℂ)} {S : Set (Sm E N)}
    (hS : ∀ φ ∈ S, TypeB K W φ) {φ : Sm E N} (hφ : φ ∈ Submodule.span ℂ S) : TypeB K W φ := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => exact ⟨fun _ _ _ => rfl, fun _ => W.zero_mem⟩
  | add x y _ _ hx hy =>
    refine ⟨fun u hu g => ?_, fun g => W.add_mem (hx.2 g) (hy.2 g)⟩
    show x.1 (g * finGL E N u) + y.1 (g * finGL E N u) = x.1 g + y.1 g
    rw [hx.1 u hu g, hy.1 u hu g]
  | smul c x _ hx =>
    refine ⟨fun u hu g => ?_, fun g => W.smul_mem c (hx.2 g)⟩
    show c • x.1 (g * finGL E N u) = c • x.1 g
    rw [hx.1 u hu g]

theorem hullGen : HullGen := by
  intro E _ _ _ N K W S hS hfd
  have hst : _root_.GlobalTheory.CuspRep.IsStable (hull S) := fun o φ hφ =>
    Submodule.mem_sInf.2 fun U hU => hU.2 o φ (Submodule.mem_sInf.1 hφ U hU)
  refine ⟨hst, ?_⟩
  have hsub : S ⊆ hull S := fun φ hφ => Submodule.mem_sInf.2 fun U hU => hU.1 hφ
  obtain ⟨t, ht⟩ := (Submodule.fg_iff_finiteDimensional _).2 hfd
  have htS : ∀ φ ∈ t, φ ∈ Submodule.span ℂ S := fun φ hφ => ht ▸ Submodule.subset_span hφ
  refine ⟨t, fun φ hφ => typeB_of_mem_span hS (htS φ hφ), fun φ hφ => ?_, fun U' hU' htU => ?_⟩
  · exact (Submodule.span_le.2 hsub) (htS φ hφ)
  · refine sInf_le ⟨?_, hU'⟩
    have h : Submodule.span ℂ S ≤ U' := ht ▸ Submodule.span_le.2 htU
    exact Submodule.subset_span.trans h

end GlobalTheory.CompanionTheory.EGlue

end
