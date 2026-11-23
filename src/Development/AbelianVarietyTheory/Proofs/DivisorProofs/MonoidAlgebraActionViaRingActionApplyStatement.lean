module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoidAlgebraActionViaRingActionApply
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Definitions.Divisors.KottwitzDimSignatureOneOne

@[expose] public section

open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

theorem _root_.GlobalTheory.T.finrank_ksSub_quotient_augmentation_of_two_roots : ∀ {k O C Idx H : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O] [CommRing C] [Algebra C O] [Fintype Idx] [FiniteDimensional k H] (σ : O →+* Module.End k H) (χ : Idx → C →+* k), Function.Injective χ → ∀ (Fil : Submodule k H), (∀ a, ∀ x ∈ Fil, σ a x ∈ Fil) → ∀ (ω : C) (r₀ r₁ : k), r₀ ≠ r₁ → (σ (algebraMap C O ω) - r₀ • 1) * (σ (algebraMap C O ω) - r₁ • 1) = 0 → (∀ i, χ i ω = r₀) → ∀ (hG : ∀ a, ∀ x ∈ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1), σ a x ∈ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1)) (hZ : ∀ a, ∀ x ∈ jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)), σ a x ∈ jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1))), jSub σ χ ⊤ ≤ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1) → ∀ (i : Idx), let G := Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1); let Z := jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)); let σW := qAct (rAct σ G hG) (Z.comap G.subtype) (fun a x hx => hZ a x hx); finrank k ((G ⧸ Z.comap G.subtype) ⧸ mSub σW (χ i) ⊤) + finrank k (H ⧸ (G ⊔ mSub σ (χ i) ⊤)) = finrank k (H ⧸ mSub σ (χ i) ⊤) := by
  first | (exact @GlobalTheory.HTRho.FilDim.finrank_fildim) | (exact GlobalTheory.HTRho.FilDim.finrank_fildim) | (intros; apply GlobalTheory.HTRho.FilDim.finrank_fildim  <;> assumption)
