module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem exists_sec_sum_nonzero :
    ∀ (X : Scheme.{0}) (L : LB X) (κ : Type) [Fintype κ] (r : κ → Γ(X, ⊤)) (σ : κ → LB.Sec L),
      ∃ s : LB.Sec L, ∀ (z : X) (i : κ), z ∈ X.basicOpen (r i) → z ∈ nonzeroLocus (σ i) →
        (∀ j, j ≠ i → z ∉ X.basicOpen (r j)) → z ∈ nonzeroLocus s := by
  intro X L κ _ r σ
  classical
  have hres : ∀ {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (a : Γ(X, U)),
      (X.presheaf.map (homOfLE h2).op).hom ((X.presheaf.map (homOfLE h1).op).hom a) =
        (X.presheaf.map (homOfLE (h2.trans h1)).op).hom a := by
    intro U V W h1 h2 a
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
  let s : LB.Sec L :=
    { f := fun m => ∑ j, (X.presheaf.map (homOfLE (le_top : L.U m ≤ ⊤)).op).hom (r j) * (σ j).f m
      compat := fun m n => by

        simp only [map_sum, map_mul, Finset.mul_sum, hres]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [(σ j).compat m n]
        ring }
  refine ⟨s, fun z i hri hσi hrj => ?_⟩
  obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.1 hσi
  have hzm : z ∈ L.U m := X.basicOpen_le _ hm
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨m, ?_⟩
  rw [Scheme.mem_basicOpen X _ z hzm] at hm ⊢
  have hgerm : ∀ j, (X.presheaf.germ (L.U m) z hzm).hom
      ((X.presheaf.map (homOfLE (le_top : L.U m ≤ ⊤)).op).hom (r j)) =
        (X.presheaf.germ ⊤ z trivial).hom (r j) := fun j =>
    TopCat.Presheaf.germ_res_apply _ _ _ _ _

  simp only [s, map_sum, map_mul, hgerm]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hu : IsUnit ((X.presheaf.germ ⊤ z trivial).hom (r i) * (X.presheaf.germ (L.U m) z hzm).hom ((σ i).f m)) :=
    ((Scheme.mem_basicOpen_top X _ z).1 hri).mul hm
  have hmax : ∑ j ∈ Finset.univ.erase i, (X.presheaf.germ ⊤ z trivial).hom (r j) *
      (X.presheaf.germ (L.U m) z hzm).hom ((σ j).f m) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z) := by
    refine Ideal.sum_mem _ fun j hj => Ideal.mul_mem_right _ _ ?_
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← Scheme.mem_basicOpen_top]
    exact hrj j (Finset.ne_of_mem_erase hj)
  by_contra hn
  have : (X.presheaf.germ ⊤ z trivial).hom (r i) * (X.presheaf.germ (L.U m) z hzm).hom ((σ i).f m) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk z) := by
    have h2 : _ ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z) := (IsLocalRing.mem_maximalIdeal _).2 hn
    simpa using Ideal.sub_mem _ h2 hmax
  exact (IsLocalRing.mem_maximalIdeal _).1 this hu

end GlobalTheory
