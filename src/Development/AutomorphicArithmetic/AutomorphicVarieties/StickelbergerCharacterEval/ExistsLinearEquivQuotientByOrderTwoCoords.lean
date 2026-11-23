module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemSpanOrderTwoRelationIffCoordsEqZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

theorem UpperTheory.V.B5.exists_linearEquiv_quotientByOrderTwo_coords :
    ∀ {A : Type} [CommRing A] {Γ : Type} [CommGroup Γ] [Finite Γ] (c : Γ) (ε : ℤ), c * c = 1 → c ≠ 1 → ε * ε = 1 → ∃ e : Rq A c ε ≃ₗ[A] (Qc c → A), ∀ w : MonoidAlgebra A Γ, e (cls A c ε w) = coord c ε w := by
  intro A _ Γ _ _ c ε hc hc1 hε
  classical
  haveI : Fintype (Qc c) := Fintype.ofFinite (Qc c)
  let f : MonoidAlgebra A Γ →ₗ[A] (Qc c → A) :=
    { toFun := coord c ε
      map_add' := by
        intro x y
        funext i
        simp only [coord, MonoidAlgebra.coeff_add, Finsupp.add_apply, Pi.add_apply]
        ring
      map_smul' := by
        intro a x
        funext i
        simp only [coord, MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul,
          RingHom.id_apply, Pi.smul_apply]
        ring }
  have hf : ∀ w, f w = coord c ε w := fun w => rfl
  have hker : LinearMap.ker f = (Ideal.span {rel A c ε}).restrictScalars A := by
    ext w
    rw [LinearMap.mem_ker, Submodule.restrictScalars_mem, mem_span_orderTwoRelation_iff_coords_eq_zero c ε hc hc1 hε, hf]
  have hrepinj : ∀ i i' : Qc c, rep i = rep i' → i = i' := by
    intro i i' h
    rw [← mk_rep i, ← mk_rep i', h]
  have hcrep : ∀ i i' : Qc c, rep i' ≠ c * rep i := by
    intro i i' h
    have e1 : i' = i := by
      rw [← mk_rep i', ← mk_rep i, h]
      exact ((mk_eq_mk hc (rep i) (c * rep i)).mpr (Or.inr rfl)).symm
    subst e1
    have e2 : c * rep i' = 1 * rep i' := by rw [← h, one_mul]
    exact hc1 (mul_right_cancel e2)
  have hsurj : Function.Surjective f := by
    intro v
    refine ⟨∑ i, MonoidAlgebra.single (rep i) (v i), ?_⟩
    funext i0
    rw [hf, coord]
    simp only [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.finsetSum_apply,
      Finsupp.single_apply]
    rw [Finset.sum_eq_single i0, Finset.sum_eq_zero]
    · simp
    · intro i _
      rw [if_neg (hcrep i0 i)]
    · intro i _ hi
      rw [if_neg (fun h => hi (hrepinj i i0 h))]
    · intro h
      exact absurd (Finset.mem_univ i0) h
  let e : Rq A c ε ≃ₗ[A] (Qc c → A) :=
    (Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {rel A c ε})).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ hker.symm ≪≫ₗ f.quotKerEquivOfSurjective hsurj
  exact ⟨e, fun w => rfl⟩
