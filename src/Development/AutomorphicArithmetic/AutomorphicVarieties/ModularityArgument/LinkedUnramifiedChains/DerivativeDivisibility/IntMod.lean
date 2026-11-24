module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CmpPrime
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Polynomial

namespace UpperTheory.V.J

section

variable {O Λ B : Type} [CommRing O] [CommRing Λ] [CommRing B] [Algebra O Λ] [Algebra O B]
  (lam : Λ →ₐ[O] B) (M : Type) [AddCommGroup M] [Module B M] [Module Λ M]
  (hs : ∀ (a : Λ) (m : M), a • m = lam a • m)

private theorem actL_pow (a : B) (n : ℕ) (m : M) :
    ((actL lam M hs a) ^ n) m = (a ^ n) • m := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, mul_smul]
    rfl

private theorem act_eval (a : B) (q : Λ[X]) (m : M) :
    q.eval₂ (lam : Λ →+* B) a • m = (aeval (actL lam M hs a) q) m := by
  refine Polynomial.induction_on' q (fun p r hp hr => ?_) (fun n c => ?_)
  · rw [eval₂_add, add_smul, hp, hr, map_add (f := _), LinearMap.add_apply]
  · rw [eval₂_monomial, aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      actL_pow, mul_smul, hs]
    rfl

end

end UpperTheory.V.J

theorem UpperTheory.V.J.intMod :
    UpperTheory.V.J.IntMod := by
  intro O Λ B _ _ _ _ _ _ lam J M _ _ _ d a
  have := d.free
  have := d.fin
  refine ⟨(actL lam M d.hs a).charpoly, (actL lam M d.hs a).charpoly_monic, ?_⟩
  have hann : eval₂ (lam : Λ →+* B) a (actL lam M d.hs a).charpoly ∈ Module.annihilator B M := by
    rw [Module.mem_annihilator]
    intro m
    rw [act_eval lam M d.hs, LinearMap.aeval_self_charpoly]
    rfl
  generalize eval₂ (lam : Λ →+* B) a (actL lam M d.hs a).charpoly = x at hann ⊢
  rw [← d.rad.radical, Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro p ⟨hJp, hp⟩
  exact (d.supp p hp).2 hJp hann
