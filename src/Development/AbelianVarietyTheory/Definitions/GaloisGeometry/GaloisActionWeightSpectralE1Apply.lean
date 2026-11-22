module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime]

theorem pullHQ_map_id (E : Spc) (n i : ℤ) : pullHQ l (𝟙 E) n i = LinearMap.id := by
  unfold pullHQ; rw [pullHl_id]; exact LinearMap.baseChange_id

theorem pullHQ_map_comp {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (n i : ℤ) :
    pullHQ l (f ≫ g) n i = pullHQ l f n i ∘ₗ pullHQ l g n i := by
  unfold pullHQ; rw [pullHl_comp]; exact LinearMap.baseChange_comp _ _

end GlobalTheory.EtC.WSS

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime]

variable {ι : Type} [Fintype ι] [LinearOrder ι] {Z : Scheme.{0}} (J : ι → Z.IdealSheafData)

end GlobalTheory.EtC.WSS

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime] {ι : Type} [Fintype ι] [LinearOrder ι] {Z : Scheme.{0}} (J : ι → Z.IdealSheafData)

end GlobalTheory.EtC.WSS

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime] {ι : Type} [Fintype ι] [LinearOrder ι] {Z : Scheme.{0}} (J : ι → Z.IdealSheafData)

end GlobalTheory.EtC.WSS

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime] {ι : Type} [Fintype ι] [LinearOrder ι]

section Galois

variable {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {V : Scheme.{0}} (p : V ⟶ Spec (CommRingCat.of k))
  (I : ι → V.IdealSheafData)

variable (a b w : ℤ)

end Galois

end GlobalTheory.EtC.WSS
