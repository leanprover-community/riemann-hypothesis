module

public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactTer

@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H.Inh

open Formalism.L2.Th1.H
open Formalism.L2.Th1.F (cmPair cmTheta)

theorem relIdx_ne_zero_of_fg {V : Type} [AddCommGroup V] [Module ℂ V] (M M' : AddSubgroup V) [AddGroup.FG M]
    (N : ℕ) (hN : 0 < N) (h : ∀ x ∈ M, N • x ∈ M') : relIdx M' M ≠ 0 := by
  have ht : IsAddTorsion (M ⧸ M'.addSubgroupOf M) := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      rw [isOfFinAddOrder_iff_nsmul_eq_zero]
      refine ⟨N, hN, ?_⟩
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
      exact h x x.2
  have := AddCommGroup.finite_of_fg_isAddTorsion _ ht
  exact AddSubgroup.index_ne_zero_of_finite

instance stdLat_fg (L : PeriodPair) (m : Type) [Finite m] : AddGroup.FG (stdLat L m) := by
  rw [← Module.Finite.iff_addGroup_fg]
  have : Module.Finite ℤ L.lattice := ZLattice.module_finite ℝ L.lattice
  let e : (m → L.lattice) ≃+ stdLat L m :=
    { toFun := fun f => ⟨fun i => (f i : ℂ), (mem_stdLat L m _).2 fun i => (f i).2⟩
      invFun := fun x i => ⟨x.1 i, (mem_stdLat L m _).1 x.2 i⟩
      left_inv := fun f => rfl
      right_inv := fun x => rfl
      map_add' := fun f g => rfl }
  exact Module.Finite.equiv e.toIntLinearEquiv

instance imgLat_fg {V : Type} [AddCommGroup V] [Module ℂ V] (g : V →ₗ[ℂ] V) (M : AddSubgroup V) [AddGroup.FG M] :
    AddGroup.FG (imgLat g M) :=
  AddGroup.fg_of_surjective (f := g.toAddMonoidHom.addSubgroupMap M) (g.toAddMonoidHom.addSubgroupMap_surjective M)

variable (n : Type) [Fintype n] [DecidableEq n]

end Formalism.L2.Th1.H.Inh
