module

public import Development.AbelianVarietyTheory.Definitions.Divisors.KottwitzDimSignatureOneOne
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.UPel.Sm.KSCount

open Module GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

section Gen

variable {k H O : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O]

theorem ksDim_finrank [FiniteDimensional k H] (ρ : O →+* Module.End k H) (φ : LinearMap.BilinForm k H)
    (Fil Z : Submodule k H) : KSDim ρ φ Fil Z (finrank k ((ksSub ρ φ Fil Z).map (cls Fil))) := by
  set M := (ksSub ρ φ Fil Z).map (cls Fil) with hM
  let b := Module.finBasis k M
  have hb : ∀ i, ∃ f ∈ ksSub ρ φ Fil Z, cls Fil f = (b i : Fil →ₗ[k] H ⧸ Fil) := fun i => (b i).2
  choose f hf hfb using hb
  have key : ∀ (g : H →ₗ[k] H) (c : Fin (finrank k M) → k),
      (∀ x ∈ Fil, g x - ∑ i, c i • f i x ∈ Fil) ↔
        cls Fil g = ∑ i, c i • (b i : Fil →ₗ[k] H ⧸ Fil) := fun g c => by
    simp_rw [← hfb]

    simp only [← map_smul, ← map_sum, cls_eq_iff, LinearMap.sum_apply, LinearMap.smul_apply]
  refine ⟨f, hf, fun g hg => ?_⟩
  let m : M := ⟨cls Fil g, g, hg, rfl⟩
  have hsum : ∀ c : Fin (finrank k M) → k, (cls Fil g = ∑ i, c i • (b i : Fil →ₗ[k] H ⧸ Fil)) ↔
      m = ∑ i, c i • b i := fun c => by
    rw [Subtype.ext_iff]; simp [m]
  refine ⟨b.equivFun m, (key g _).2 ((hsum _).2 ?_), fun c hc => ?_⟩
  · rw [← b.equivFun_symm_apply, LinearEquiv.symm_apply_apply]
  · have := (hsum c).1 ((key g c).1 hc)
    rw [this, ← b.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

theorem finrank_map_add_ker {M N : Type*} [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [AddCommGroup N] [Module k N] (p : Submodule k M) (f : M →ₗ[k] N) :
    finrank k (p.map f) + finrank k (LinearMap.ker (f ∘ₗ p.subtype)) = finrank k p := by
  rw [← LinearMap.finrank_range_add_finrank_ker (f ∘ₗ p.subtype), LinearMap.range_comp,
    Submodule.range_subtype]

end Gen

end GlobalTheory.UPel.Sm.KSCount
