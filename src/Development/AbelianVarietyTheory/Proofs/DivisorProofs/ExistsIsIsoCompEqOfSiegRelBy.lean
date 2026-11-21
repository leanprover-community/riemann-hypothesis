import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLevelOn
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRankAt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeQuotientByFiniteTranslations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegRel
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedSpaceOfIsConnected
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveQcPow
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMonHomFactorOfFlatSurjective

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionRigid

variable {S : Scheme.{0}}

lemma comp_mulN {G : Over S} [GrpObj G] {T : Over S} (x : T ⟶ G) (N : ℕ) : x ≫ mulN G N = x ^ N := by
  induction N with
  | zero =>
    rw [pow_zero, mulN, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  | succ n ih => rw [pow_succ, mulN, ← Category.assoc, comp_lift, ih, Category.comp_id, Hom.mul_def]

def tLift {G : Over S} [GrpObj G] {N : ℕ} {T : Over S} (x : T ⟶ G) (hx : x ^ N = 1) : T ⟶ torsion G N :=
  pullback.lift x (toUnit T) (by rw [comp_mulN, hx, Hom.one_def])

lemma tLift_ι {G : Over S} [GrpObj G] {N : ℕ} {T : Over S} (x : T ⟶ G) (hx : x ^ N = 1) :
    tLift x hx ≫ torsion.ι G N = x :=
  pullback.lift_fst _ _ _

lemma ι_pow (G : Over S) [GrpObj G] (N : ℕ) : torsion.ι G N ^ N = 1 := by
  rw [← comp_mulN, Hom.one_def]
  refine (pullback.condition (f := mulN G N) (g := η[G])).trans ?_
  congr 1
  exact toUnit_unique _ _

instance mono_ι (G : Over S) [GrpObj G] (N : ℕ) : Mono (torsion.ι G N) := by
  have : Mono η[G] := ⟨fun _ _ _ => toUnit_unique _ _⟩
  exact inferInstanceAs (Mono (pullback.fst _ _))

end GlobalTheory.TorsionRigid

namespace GlobalTheory.TorsionRigid

end GlobalTheory.TorsionRigid
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

namespace GlobalTheory.UPel.HT.SiegFactor

theorem comp_id_pow {S : Scheme.{0}} {T A : Over S} [GrpObj A] (x : T ⟶ A) (k : ℕ) :
    x ≫ (𝟙 A) ^ k = x ^ k := by
  rw [MonObj.comp_pow, Category.comp_id]

theorem id_pow_comp {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (χ : A ⟶ B) [IsMonHom χ]
    (k : ℕ) : ((𝟙 A) ^ k) ≫ χ = χ ≫ (𝟙 B) ^ k := by
  rw [MonObj.pow_comp, Category.id_comp, comp_id_pow]

theorem isMonHom_epi_id_pow {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) {k : ℕ}
    (hk : 0 < k) : IsMonHom ((𝟙 A) ^ k) ∧ Epi ((𝟙 A) ^ k) := by
  have := hA.comm
  have hm : IsMonHom ((𝟙 A) ^ k) := GlobalTheory.AbLaw.MulN.isMonHom_mulA A k
  obtain ⟨hfl, hsu, hqc⟩ := SiegUniqBase.flat_surjective_qc_pow S A hA k hk
  exact ⟨hm, (GlobalTheory.exists_monHom_factor_of_flat_surjective S A A A _ _ hm hm hfl hsu hqc
    fun _ _ h => h).2⟩

end GlobalTheory.UPel.HT.SiegFactor

namespace GlobalTheory.UPel.HT

end GlobalTheory.UPel.HT
end
