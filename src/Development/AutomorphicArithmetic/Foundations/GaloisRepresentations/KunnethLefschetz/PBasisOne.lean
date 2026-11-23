module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
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
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

namespace UpperTheory.Gal.KunnethLefschetz

theorem basisOne_holds : BasisOne := by
  intro F M _ _ _ _ lam hlam
  by_cases h0 : lam = 0
  · haveI := hlam h0
    exact ⟨0, Module.Basis.empty M, fun t => t.elim0⟩
  obtain ⟨x, hx⟩ : ∃ x, lam x ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (LinearMap.ext hc)
  set v : M := (lam x)⁻¹ • x with hvdef
  have hv : lam v = 1 := by
    rw [hvdef, map_smul, smul_eq_mul, inv_mul_cancel₀ hx]
  set N := LinearMap.ker lam
  let e := Module.finBasis F N
  let f : Fin (Module.finrank F N + 1) → M := Fin.cons v (fun i => v + (e i : M))
  have hrange : LinearMap.range lam = ⊤ := by
    rw [eq_top_iff]
    intro c _
    exact ⟨c • v, by rw [map_smul, hv, smul_eq_mul, mul_one]⟩
  have hcard : Fintype.card (Fin (Module.finrank F N + 1)) = Module.finrank F M := by
    rw [Fintype.card_fin, ← LinearMap.finrank_range_add_finrank_ker lam, hrange, finrank_top,
      Module.finrank_self, add_comm]
  have hvmem : v ∈ Submodule.span F (Set.range f) :=
    Submodule.subset_span ⟨0, by simp [f]⟩
  have hemem : ∀ i, (e i : M) ∈ Submodule.span F (Set.range f) := by
    intro i
    have h1 : v + (e i : M) ∈ Submodule.span F (Set.range f) :=
      Submodule.subset_span ⟨i.succ, by simp [f]⟩
    have := Submodule.sub_mem _ h1 hvmem
    simpa using this
  have hNmem : ∀ y : N, (y : M) ∈ Submodule.span F (Set.range f) := by
    intro y
    rw [← e.sum_repr y]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hemem i))
  have hspan : ⊤ ≤ Submodule.span F (Set.range f) := by
    intro z _
    have hz : z - lam z • v ∈ N := by
      rw [LinearMap.mem_ker, map_sub, map_smul, hv, smul_eq_mul, mul_one, sub_self]
    have h2 := hNmem ⟨_, hz⟩
    have h3 := Submodule.add_mem _ h2 (Submodule.smul_mem _ (lam z) hvmem)
    simpa using h3
  refine ⟨_, basisOfTopLeSpanOfCardEqFinrank f hspan hcard, fun t => ?_⟩
  rw [coe_basisOfTopLeSpanOfCardEqFinrank]
  refine Fin.cases ?_ (fun i => ?_) t
  · simpa [f] using hv
  · have hk : lam (e i : M) = 0 := (e i).2
    simp [f, hv, hk]

end UpperTheory.Gal.KunnethLefschetz
