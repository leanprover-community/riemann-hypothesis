module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Definitions.Divisors.KottwitzDimSignatureOneOne
public import Mathlib.LinearAlgebra.Isomorphisms

@[expose] public section

open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

namespace GlobalTheory.HTRho

theorem mSub_qAct_top {k O C : Type*} {H : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O] [CommRing C]
    [Algebra C O] (σ : O →+* Module.End k H) (G : Submodule k H) (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G)
    (χ : C →+* k) : mSub (qAct σ G hG) χ ⊤ = (mSub σ χ ⊤).map G.mkQ := by
  unfold mSub
  rw [Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨c, x, -, rfl⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective G x
    refine ⟨σ (algebraMap C O c) y - χ c • y, ⟨c, y, trivial, rfl⟩, ?_⟩
    rw [map_sub, map_smul]
    rfl
  · rintro ⟨w, ⟨c, y, -, rfl⟩, rfl⟩
    refine ⟨c, G.mkQ y, trivial, ?_⟩
    rw [map_sub, map_smul, qAct_mk]

theorem quotFacts {k O C Idx H : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O] [CommRing C]
    [Algebra C O] (σ : O →+* Module.End k H) (G : Submodule k H) (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G)
    (χ : Idx → C →+* k) :
    (jSub σ χ ⊤ ≤ G → jSub (qAct σ G hG) χ ⊤ = ⊥) ∧
      ∀ i, finrank k ((H ⧸ G) ⧸ mSub (qAct σ G hG) (χ i) ⊤) = finrank k (H ⧸ (G ⊔ mSub σ (χ i) ⊤)) := by
  refine ⟨fun hJ => ?_, fun i => ?_⟩
  · unfold jSub
    rw [Submodule.span_eq_bot]
    rintro z ⟨r, lam, c, x, -, hc, rfl⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective G x
    have hmem : (∑ l, lam l • σ (algebraMap C O (c l)) y) ∈ G :=
      hJ (Submodule.subset_span ⟨r, lam, c, y, trivial, hc, rfl⟩)
    have : (∑ l, lam l • qAct σ G hG (algebraMap C O (c l)) (Submodule.Quotient.mk y)) =
        G.mkQ (∑ l, lam l • σ (algebraMap C O (c l)) y) := by

      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul]
      rfl
    rw [this, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hmem
  · rw [mSub_qAct_top]
    exact LinearEquiv.finrank_eq (Submodule.quotientQuotientEquivQuotientSup G (mSub σ (χ i) ⊤))

end GlobalTheory.HTRho
