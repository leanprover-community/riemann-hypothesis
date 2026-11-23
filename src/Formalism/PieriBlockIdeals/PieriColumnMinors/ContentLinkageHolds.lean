module

public import Formalism.PieriBlockIdeals.Statement
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Data.ZMod.Basic

@[expose] public section

noncomputable section

open Finset Polynomial

namespace Formalism.CohomologicalDescent

open Classical

theorem comb_roots_prod {K : Type} [Field K] {N : ℕ} (f : Fin N → K) :
    (∏ a, (X + C (f a))).roots = Multiset.map (fun a => -f a) Finset.univ.val := by
  have h : (∏ a, (X + C (f a))) =
      ((Multiset.map (fun a => -f a) Finset.univ.val).map fun x => X - C x).prod := by
    rw [Multiset.map_map, Finset.prod_eq_multiset_prod]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    simp [sub_eq_add_neg]
  rw [h, Polynomial.roots_multiset_prod_X_sub_C]

theorem contentLinkage_holds : Linkage := by
  intro l K _ _ N U U' c hl hprod
  haveI : Fact l.Prime := ⟨hl⟩
  have hr := congrArg Polynomial.roots hprod
  have hU := comb_roots_prod (fun a => (((U a + c : ℤ)) : K))
  have hU' := comb_roots_prod (fun a => (((U' a + c : ℤ)) : K))
  rw [hU, hU'] at hr
  let ψ : ZMod l →+* K := ZMod.castHom (dvd_refl l) K
  have hψ : Function.Injective ψ := ψ.injective
  have key : ∀ V : Fin N → ℤ, Multiset.map (fun a => -(((V a + c : ℤ)) : K)) Finset.univ.val =
      Multiset.map ψ (Multiset.map (fun a => -(((V a + c : ℤ)) : ZMod l)) Finset.univ.val) := by
    intro V
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro a _
    simp [ψ, map_intCast]
  rw [key U, key U'] at hr
  have h2 := Multiset.map_injective hψ hr
  have h3 := congrArg (Multiset.map fun z : ZMod l => -z - (c : ZMod l)) h2
  simp only [Multiset.map_map] at h3
  convert h3 using 2 <;> (try simp only [Function.comp_apply]; push_cast; ring)

end Formalism.CohomologicalDescent
