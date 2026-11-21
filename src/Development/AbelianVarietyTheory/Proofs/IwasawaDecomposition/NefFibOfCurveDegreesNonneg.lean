import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LineBundleIntersectionNumberGroundFieldChange

section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIntersectionNumber_groundFieldChange : ∀ (κ κ' : Type) [Field κ] [Field κ'] [Algebra κ κ'] (Z : Scheme.{0}) [Algebra κ' Γ(Z, ⊤)] [Algebra κ Γ(Z, ⊤)] [IsScalarTower κ κ' Γ(Z, ⊤)] (G : Z.Modules) {ι : Type} [Fintype ι] (L : ι → LB Z), interNum κ G L = (Module.finrank κ κ' : ℤ) * interNum κ' G L := by
  first | exact @GlobalTheory.GroundFieldChange.interNum_fieldChange | exact GlobalTheory.GroundFieldChange.interNum_fieldChange | (intros; apply GlobalTheory.GroundFieldChange.interNum_fieldChange <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.ArInt

theorem nefFib_of_primeField : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (L : HermLB p),
    (∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (q : ℕ) [Fact q.Prime]
      [Algebra (ZMod q) Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod q) (L.B.pull i) 1) →
    ArInt.NefFib L := by
  intro k _ X p L h Z i _ _ κ _ _ _ hdim
  haveI : Fintype κ := Fintype.ofFinite κ
  haveI hq : Fact (ringChar κ).Prime := ⟨CharP.char_is_prime κ (ringChar κ)⟩
  letI : Algebra (ZMod (ringChar κ)) κ := ZMod.algebra κ (ringChar κ)
  letI : Algebra (ZMod (ringChar κ)) Γ(Z, ⊤) :=
    ((algebraMap κ Γ(Z, ⊤)).comp (algebraMap (ZMod (ringChar κ)) κ)).toAlgebra
  haveI : IsScalarTower (ZMod (ringChar κ)) κ Γ(Z, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  have h1 := h Z i (ringChar κ) hdim
  have e := GlobalTheory.T.lineBundleIntersectionNumber_groundFieldChange (ZMod (ringChar κ)) κ Z (structureModule Z) (fun _ : Fin 1 => L.B.pull i)
  rw [topSelf_def] at h1 ⊢
  rw [e] at h1
  haveI : Module.Finite (ZMod (ringChar κ)) κ := Module.Finite.of_finite
  have hpos : (0 : ℤ) < (Module.finrank (ZMod (ringChar κ)) κ : ℤ) := by
    exact_mod_cast Module.finrank_pos
  exact (mul_nonneg_iff_of_pos_left hpos).mp h1

end GlobalTheory.ArInt
end
