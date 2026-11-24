module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace PI.InvIdealIdxPiWork

open NumberField nonZeroDivisors

theorem map_compLeft_pi {ι : Type} {G G' : Type*} [AddGroup G] [AddGroup G'] (φ : G →+ G')
    (A : ι → AddSubgroup G) :
    (AddSubgroup.pi Set.univ A).map (φ.compLeft ι) =
      AddSubgroup.pi Set.univ (fun i => (A i).map φ) := by
  ext y
  simp only [AddSubgroup.mem_map, AddSubgroup.mem_pi, Set.mem_univ, true_implies, forall_const]
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    exact ⟨x i, hx i, rfl⟩
  · intro h
    choose x hx hxy using h
    exact ⟨x, hx, funext hxy⟩

theorem submodule_pi_toAddSubgroup {ι : Type} {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (p : ι → Submodule R M) :
    (Submodule.pi Set.univ p).toAddSubgroup =
      AddSubgroup.pi Set.univ (fun i => (p i).toAddSubgroup) := by
  ext x
  simp only [Submodule.mem_toAddSubgroup, Submodule.mem_pi, AddSubgroup.mem_pi]

variable {E : Type} [Field E] [NumberField E]

abbrev idS (I : Ideal (𝓞 E)) : AddSubgroup E :=
  ((I : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E).toAddSubgroup

theorem idS_eq_map (I : Ideal (𝓞 E)) :
    idS I = I.toAddSubgroup.map (algebraMap (𝓞 E) E).toAddMonoidHom := by
  ext x
  simp only [idS, Submodule.mem_toAddSubgroup, FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal,
    AddSubgroup.mem_map, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]

theorem relIndex_pi_idS {ι : Type} [Fintype ι] (I : ι → Ideal (𝓞 E)) :
    (AddSubgroup.pi Set.univ (fun i => idS (I i))).relIndex
      (AddSubgroup.pi Set.univ (fun _ : ι => idS (E := E) ⊤)) = ∏ i, Ideal.absNorm (I i) := by
  have hinj : Function.Injective ((algebraMap (𝓞 E) E).toAddMonoidHom.compLeft ι) := by
    intro x y h
    funext i
    exact IsFractionRing.injective (𝓞 E) E (congrFun h i)
  have htop : AddSubgroup.pi Set.univ (fun _ : ι => (⊤ : Ideal (𝓞 E)).toAddSubgroup) = ⊤ := by
    ext x
    simp [AddSubgroup.mem_pi]
  simp_rw [idS_eq_map]
  rw [← map_compLeft_pi (algebraMap (𝓞 E) E).toAddMonoidHom (fun i => (I i).toAddSubgroup),
    ← map_compLeft_pi (algebraMap (𝓞 E) E).toAddMonoidHom (fun _ : ι => (⊤ : Ideal (𝓞 E)).toAddSubgroup),
    AddSubgroup.relIndex_map_map_of_injective _ _ hinj, htop, AddSubgroup.relIndex_top_right,
    AddSubgroup.index_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Ideal.absNorm_apply]
  rfl

end PI.InvIdealIdxPiWork

end
