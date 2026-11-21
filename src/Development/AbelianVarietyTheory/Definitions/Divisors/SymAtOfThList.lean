import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomExtOfSecCoord

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.Ex.OneGen GlobalTheory.ThetaPtMove
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.Model


theorem length_eq {S : Scheme.{0}} (P : PolAV S) (ρ : LB.Gen (P.L.pull (eSec P.A))) (m : ℕ) {K : Type} [Field K]
    (hK : (m : K) ≠ 0) (x : Sp K ⟶ S) {θ : SecAt P.A P.L x} {N : ℕ} {pt : Fin N → (Over.mk x ⟶ P.A)} {c : Fin N → K}
    (H : ThList P.A P.L ρ m x θ pt c) : N = (m ^ 2) ^ (2 * P.g) := by
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  let i : K →+* AlgebraicClosure K := algebraMap _ _
  have hK' : ((m ^ 2 : ℕ) : AlgebraicClosure K) ≠ 0 := by
    rw [← map_natCast i, map_ne_zero, Nat.cast_pow]; exact pow_ne_zero _ hK
  let u : Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl
  rw [← TorsionFieldExt.card_torsion hL P (spMap i ≫ x) hK', ← Nat.card_fin N]
  refine Nat.card_congr (Equiv.ofBijective (fun a => ⟨u ≫ pt a, by
    rw [← MonObj.comp_pow, (H.2.1 a).1, MonObj.comp_one]⟩) ⟨fun a b h => ?_, fun p => ?_⟩)
  · exact H.1 (TorsionFieldExt.comp_injective u _ (congrArg Subtype.val h))
  · obtain ⟨a, ha⟩ := H.2.2 _ i p.1 p.2
    exact ⟨a, Subtype.ext (Over.OverMorphism.ext ha.symm)⟩

theorem polFib_self {R : Type} [CommRing R] (P : PolAV (Sp R)) : PolFib P.A P.L P.g (𝟙 _) := by
  exact ⟨P, 𝟙 _, rfl, @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl P.A) (inferInstanceAs (IsMonHom (𝟙 P.A))),
    (GlobalTheory.PolBaseChange.lbIso_refl P.isLB).chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl)⟩


theorem symTup_perm {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) (σ : Equiv.Perm (Fin N)) :
    symTup (c ∘ σ) = symTup c := by
  funext j
  rw [symTup, symTup, ← Multiset.map_map, Multiset.map_univ_val_equiv]





theorem symTup_map {R R' : Type} [CommRing R] [CommRing R'] (i : R →+* R') {N : ℕ} (c : Fin N → R) (j : Fin N) :
    symTup (fun a => i (c a)) j = i (symTup c j) := by
  simp only [symTup, Finset.esymm_map_val, map_pow, map_sum, map_prod]

theorem thG_pull {S : Scheme.{0}} (P : PolAV S) {ρ : LB.Gen (P.L.pull (eSec P.A))} (hρ : ρ.IsGen) {m : ℕ}
    {B T : Over S} (β : B ⟶ T) {θ : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)} {y : T ⟶ P.A} {c : Γ(T.left, ⊤)}
    (H : ThG P.A P.L ρ m θ y c) : ThG P.A P.L ρ m (VVRank.pullS P.A _ β θ) (β ≫ y) (β.left.appTop.hom c) := by
  have hL := P.isLB
  have := P.isAb.comm
  have hp : IsGrpPullback P.A P.A (𝟙 _) (𝟙 P.A.left) := @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl P.A) (inferInstanceAs (IsMonHom (𝟙 P.A)))
  obtain ⟨w, hw⟩ : LBIso P.L (P.L.pull (𝟙 _)) :=
    (GlobalTheory.PolBaseChange.lbIso_refl hL).chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl)
  obtain ⟨ρ', -, hr⟩ := exists_rigidificationPullbackCompatibleIso hp hw hL hL hρ
  have hτ : β.left ≫ T.hom = B.hom ≫ 𝟙 S := by rw [Over.w, Category.comp_id]
  have hσ : 𝟙 B.left ≫ B.hom = B.hom ≫ 𝟙 S := by simp
  obtain ⟨t, ht⟩ := exists_secRel hp β.left hτ hw hL hL θ
  have hu : (β ≫ y) ^ (m ^ 2) = 1 := by rw [← MonObj.comp_pow, H.1, MonObj.comp_one]
  have hrel := secRel_smul hp β.left hτ (𝟙 B.left) hσ β (Category.id_comp _) ht
    (th' := VVRank.pullS P.A _ β θ) (c := 1) (one_smul _ _).symm
  have q := ThG.smul (th' := SecM.toSec P.A ((𝟙 B.left : B.left ⟶ B.left).appTop.hom 1 • SecM.ofSec P.A t)) hL rfl
    (ThG.move hp β.left hτ hw hL hL hr (x := β ≫ y) (by simp) hu ht H)
  have q' := ThG.up hp (𝟙 B.left) hσ hw hL hL hr (x₀ := β ≫ y) (by simp) hu hrel q
  simpa using q'




theorem thList_pull {S : Scheme.{0}} (P : PolAV S) {ρ : LB.Gen (P.L.pull (eSec P.A))} (hρ : ρ.IsGen) {m : ℕ}
    {K F : Type} [Field K] [Field F] (i : K →+* F) {x : Sp K ⟶ S} {θ : SecAt P.A P.L x} {N : ℕ}
    {pt : Fin N → (Over.mk x ⟶ P.A)} {c : Fin N → K} (H : ThList P.A P.L ρ m x θ pt c) (a : Fin N) :
    ThG P.A P.L ρ m (SecAt.pull P.A P.L θ i)
      ((Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ pt a) (GlobalTheory.ZH.fn (i (c a))) := by
  have q := thG_pull P hρ (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) (H.2.1 a)
  have e : (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x).left.appTop.hom (GlobalTheory.ZH.fn (c a)) =
      GlobalTheory.ZH.fn (i (c a)) :=
    (congrArg (fun q => q.hom (c a)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i))).symm
  rw [e] at q
  exact q


theorem hasTh₂_of_hasTh {S : Scheme.{0}} (P : PolAV S) {ρ : LB.Gen (P.L.pull (eSec P.A))} {m m' : ℕ} {K : Type}
    [Field K] {x : Sp K ⟶ S} {N N' : ℕ} {c : Fin N → K} {c' : Fin N' → K} (H : HasTh P.A P.L ρ m x c)
    (H' : HasTh P.A P.L ρ m' x c') : ∃ r : K, HasTh₂ P.A P.L ρ m m' x c fun a => r * c' a := by
  obtain ⟨θ, pt, hg, h⟩ := H
  obtain ⟨θ', pt', hg', h₁, h₂, h₃⟩ := H'
  obtain ⟨r, hr⟩ := hg' θ
  have e₁ : SecM.ofSec P.A θ = r • SecM.ofSec P.A θ' := Subtype.ext (funext hr)
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom r, θ, pt, pt', hg, h, h₁, fun a => ?_, h₃⟩
  have q := ThG.smul P.isLB e₁ (h₂ a)
  have e₂ : GlobalTheory.ZH.fn ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom r * c' a) =
      @id Γ(Sp K, ⊤) r * @id Γ(Sp K, ⊤) (GlobalTheory.ZH.fn (c' a)) :=
    (map_mul (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom _ _).trans
      (congrArg (· * _) ((Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id_apply r))
  rw [e₂]
  exact q

end GlobalTheory.UMin.Model
