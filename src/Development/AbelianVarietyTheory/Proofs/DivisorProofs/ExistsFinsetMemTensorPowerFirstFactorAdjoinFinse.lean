module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstAndFinite
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
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

theorem firstAndFinite_mono (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ)
    {F G : Finset A} (h : F ⊆ G) : firstAndFinite R A k F ≤ firstAndFinite R A k G := by
  unfold firstAndFinite
  apply Algebra.adjoin_mono
  apply Set.union_subset_union_right
  apply Set.iUnion_mono
  intro i
  exact Set.image_mono (by exact_mod_cast h)

theorem tprod_eq_prod_singleAlgHom (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ)
    (f : Fin (k + 1) → A) :
    PiTensorProduct.tprod R f = ∏ i, PiTensorProduct.singleAlgHom (R := R) (A := fun _ : Fin (k + 1) => A) i (f i) := by
  classical
  simp only [PiTensorProduct.singleAlgHom_apply]
  have := map_prod (PiTensorProduct.tprodMonoidHom R (A := fun _ : Fin (k + 1) => A))
    (fun u => MonoidHom.mulSingle (fun _ : Fin (k + 1) => A) u (f u)) Finset.univ
  refine Eq.trans ?_ this
  simp only [MonoidHom.mulSingle_apply]
  rw [Finset.univ_prod_mulSingle]
  rfl

theorem exists_finset_mem_firstAndFinite (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ)
    (x : PiTensorProduct R (fun _ : Fin (k + 1) => A)) : ∃ F : Finset A, x ∈ firstAndFinite R A k F := by
  classical
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    refine ⟨Finset.univ.image f, ?_⟩
    refine Subalgebra.smul_mem _ ?_ r
    rw [tprod_eq_prod_singleAlgHom]
    refine Subalgebra.prod_mem _ fun i _ => ?_
    apply Algebra.subset_adjoin
    refine Or.inr (Set.mem_iUnion.2 ⟨i, f i, by simp, rfl⟩)
  | add x y hx hy =>
    obtain ⟨F, hF⟩ := hx
    obtain ⟨G, hG⟩ := hy
    exact ⟨F ∪ G, Subalgebra.add_mem _ (firstAndFinite_mono R A k Finset.subset_union_left hF)
      (firstAndFinite_mono R A k Finset.subset_union_right hG)⟩

end GlobalTheory.EtC
