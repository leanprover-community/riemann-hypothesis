module

public import GroundTheory.AutomorphicForms.HarishChandraCentre.Projection
public import GroundTheory.AutomorphicForms.HarishChandraCentre.FischerForm
public import GroundTheory.AutomorphicForms.HarishChandraCentre.Fischer
public import Mathlib.Algebra.MvPolynomial.Funext
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
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace GroundTheory.Automorphic.HarishChandra

attribute [local instance 100] LieRing.ofAssociativeRing

open MvPolynomial

variable {n : ℕ}

theorem exists_adjoint (u : U n) :
    ∃ u' : U n, ∀ f g : Poly n, fischer (rho 0 u f) g = fischer f (rho 0 u' g) := by
  induction u using U.induction with
  | halg r =>
    refine ⟨algebraMap ℂ (U n) (star r), fun f g => ?_⟩
    simp only [AlgHom.commutes, Module.algebraMap_end_apply, fischer_smul_left, fischer_smul_right]
  | hι X =>
    refine ⟨∑ a : Fin n × Fin n, star (X a.1 a.2) • e (a.2, a.1), fun f g => ?_⟩
    rw [ι_eq_sum_e]

    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, fischer_sum_left,
    fischer_sum_right, fischer_smul_left, fischer_smul_right, star_star]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show e a = e (a.1, a.2) from rfl, rho_zero_e, rho_zero_e, fischer_rowOp]
  | hmul a b ha hb =>
    obtain ⟨a', ha'⟩ := ha
    obtain ⟨b', hb'⟩ := hb
    refine ⟨b' * a', fun f g => ?_⟩
    rw [map_mul, Module.End.mul_apply, ha', hb', map_mul, Module.End.mul_apply]
  | hadd a b ha hb =>
    obtain ⟨a', ha'⟩ := ha
    obtain ⟨b', hb'⟩ := hb
    refine ⟨a' + b', fun f g => ?_⟩
    rw [map_add (f := _), LinearMap.add_apply, fischer_add_left, ha', hb', map_add (f := _), LinearMap.add_apply,
      fischer_add_right]

theorem eq_zero_of_mem_center_of_hcProjLin_eq_zero {z : U n}
    (hz : z ∈ Subalgebra.center ℂ (U n)) (h : hcProjLin z = 0) : z = 0 := by
  obtain ⟨z', hz'⟩ := exists_adjoint z
  have hc : ∀ u : U n, u * z = z * u := fun u => (Subalgebra.mem_center_iff.1 hz) u
  apply eq_zero_of_rho_zero_eq_zero
  refine eq_zero_of_forall_highestWeight (rho 0 z) (rho 0 z') ?_ hz' ?_ ?_
  · intro i j
    rw [← rho_zero_e, ← map_mul, ← map_mul, hc]
  · rw [← map_mul, ← map_mul, hc]
  · intro v μ hup hwt
    have := rep_apply_of_highestWeight (rho 0) (fun i => (μ i : ℂ)) (v := v)
      (fun a ha => by
        rw [show e a = e (a.1, a.2) from rfl, rho_zero_e]
        exact hup a.1 a.2 ha)
      (fun k => by rw [rho_zero_e]; exact rowOp_self_of_wtProj μ v k hwt)
      (fun k => hc (e (k, k)))
    rw [this, h, map_zero, zero_smul]

theorem hcProjLin_injOn_center :
    Set.InjOn (hcProjLin (n := n)) (Subalgebra.center ℂ (U n) : Set (U n)) := by
  intro z hz z' hz' h
  have := eq_zero_of_mem_center_of_hcProjLin_eq_zero (Subalgebra.sub_mem _ hz hz')
    (by rw [map_sub, h, sub_self])
  exact sub_eq_zero.1 this

theorem translate_neg_translate (c : Fin n → ℂ) (p : MvPolynomial (Fin n) ℂ) :
    translate (-c) (translate c p) = p := by
  refine MvPolynomial.funext fun lam => ?_
  rw [eval_translate, eval_translate, neg_add_cancel_right]

theorem translate_injective (c : Fin n → ℂ) : Function.Injective (translate (n := n) c) :=
  Function.LeftInverse.injective (translate_neg_translate c)

theorem harishChandraHom_injective : Function.Injective (harishChandraHom (n := n)) := by
  intro z z' h
  rw [harishChandraHom_apply, harishChandraHom_apply] at h
  exact Subtype.ext (hcProjLin_injOn_center z.2 z'.2 (translate_injective _ h))

end GroundTheory.Automorphic.HarishChandra
