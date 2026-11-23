module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGluing.LocGlueOfPair
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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

open ValuativeRel
open Formalism.MainNotions.S.Loc

namespace PI.LocHerm.Glue

theorem rieszRepresentation_holds : Riesz := by
  intro F _ _ _ E _ _ _ _ M V _ _ H f
  have : Module.Free F E := M.L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  have : Module.Free E V := H.free
  have : Module.Finite E V := H.fin
  let b := Module.Free.chooseBasis E V
  let ℓ : V → V →ₗ[E] E := fun y =>
    { toFun := fun v => H.h v y
      map_add' := fun v w => H.h_add_left v w y
      map_smul' := fun c v => by
        simp only [RingHom.id_apply, smul_eq_mul]
        exact H.h_smul_left c v y }
  have hℓ : ∀ v y, ℓ y v = H.h v y := fun _ _ => rfl
  have key : ∀ (v : V) (a : Module.Free.ChooseBasisIndex E V → E),
      H.h v (∑ j, a j • b j) = ∑ j, M.L.cj (a j) * H.h v (b j) := by
    intro v a
    rw [H.h_herm (∑ j, a j • b j) v]
    have hs : H.h (∑ j, a j • b j) v = ∑ j, a j * H.h (b j) v := by

      rw [← hℓ, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, hℓ, smul_eq_mul]

    rw [hs, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← H.h_herm]
  let A : Matrix (Module.Free.ChooseBasisIndex E V) (Module.Free.ChooseBasisIndex E V) E :=
    Matrix.of fun i j => H.h (b i) (b j)
  have hA : ∀ u i, H.h (b i) (∑ j, M.L.cj (u j) • b j) = A.mulVecLin u i := by
    intro u i
    rw [key, Matrix.mulVecLin_apply]
    simp only [M.L.cj_cj, Matrix.mulVec, dotProduct, A, Matrix.of_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hext : ∀ (x : V) (g : V →ₗ[E] E), (∀ i, H.h (b i) x = g (b i)) → ∀ v, H.h v x = g v := by
    intro x g hg v
    have : ℓ x = g := b.ext fun i => by rw [hℓ]; exact hg i
    rw [← hℓ, this]
  have hinj : Function.Injective A.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have hx : ∀ v, H.h v (∑ j, M.L.cj (u j) • b j) = (0 : V →ₗ[E] E) v := by
      refine hext _ 0 fun i => ?_
      rw [hA, hu]
      rfl
    have hx0 : (∑ j, M.L.cj (u j) • b j) = 0 := by
      refine H.nondeg _ fun y => ?_
      rw [H.h_herm y, hx y, LinearMap.zero_apply, map_zero]
    have hc : (fun j => M.L.cj (u j)) = 0 := by
      apply b.equivFun.symm.injective
      rw [Module.Basis.equivFun_symm_apply, hx0, map_zero]
    funext j
    have := congrFun hc j
    simp only [Pi.zero_apply] at this
    have h2 := congrArg M.L.cj this
    rw [M.L.cj_cj, map_zero] at h2
    exact h2
  obtain ⟨u, hu⟩ := IsArtinian.surjective_of_injective_endomorphism A.mulVecLin hinj
    (fun i => f (b i))
  refine ⟨∑ j, M.L.cj (u j) • b j, hext _ f fun i => ?_⟩
  rw [hA, hu]

end PI.LocHerm.Glue
