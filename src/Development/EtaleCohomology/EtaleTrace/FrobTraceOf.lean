module

public import Development.EtaleCohomology.EtaleTrace.LadicH0LocallyConstant

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace

theorem pb_comp (l : ℕ) [Fact l.Prime] {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (n : ℤ) :
    pb l (f ≫ g) n = pb l f n ∘ₗ pb l g n := by
  unfold pb pullHQ
  rw [Functor.map_comp, pullHl_comp, LinearMap.baseChange_comp]

end LateralTheory.EtaleTrace

end
