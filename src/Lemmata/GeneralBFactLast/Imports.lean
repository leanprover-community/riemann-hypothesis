module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic

@[expose] public section

universe u_1 u_2

namespace Bl.general_b_fact'''''''

theorem goal1 :
  ∀ {O : Type u_1} [CommRing.{u_1} O] [IsDomain.{u_1} O] [IsDiscreteValuationRing.{u_1} O]
  {ι : Type u_2} (s : Finset.{u_2} ι) (a : ι → O),
  Eq.{1}
    (DFunLike.coe.{u_1 + 1, u_1 + 1, 1} (IsDiscreteValuationRing.addVal.{u_1} O)
      (Finset.prod.{u_2, u_1} s fun (i : ι) ↦ a i))
    (Finset.sum.{u_2, 0} s fun (i : ι) ↦
      DFunLike.coe.{u_1 + 1, u_1 + 1, 1} (IsDiscreteValuationRing.addVal.{u_1} O) (a i)) := by
  intro O _ _ _ ι s a
  exact map_prod (AddValuation.toValuation (IsDiscreteValuationRing.addVal O)) a s

end Bl.general_b_fact'''''''
