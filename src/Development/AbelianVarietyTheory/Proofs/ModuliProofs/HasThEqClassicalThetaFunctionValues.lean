import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AppellHumbertUniformisationRiemannFormStatement
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsBasisOfIsField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExAtMemPairChartIff
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasAnConstThetaGrpZeroIff
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_const_mul_of_isFnPow_ne_zero (hH : Out.GlobalSectionsRankAlgClosed) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g)
    (θ : (Fin P.g → ℂ) → ℂ) (hθ : θ ≠ 0) (s : (lbPow P.L 1).Sec) (hs : u.IsFnPow 1 s θ) (t : (lbPow P.L 1).Sec) :
    ∃ a : ℂ, ∀ j, t.f j = constFn P.A.hom _ a * s.f j := by
  obtain ⟨β, hβ⟩ := PowSec.exists_basis_sections hH ℂ P 1 le_rfl
  have i₀ : Fin (1 ^ P.g) := ⟨0, by simp⟩
  have su : ∀ {M : Type} [AddCommMonoid M] (q : Fin (1 ^ P.g) → M), ∑ i, q i = q i₀ := fun q =>
    Finset.sum_eq_single i₀ (fun a _ h => absurd (Fin.ext (by have := a.2; have := i₀.2; simp at *; omega)) h) (by simp)
  obtain ⟨a, ha, -⟩ := hβ s
  obtain ⟨b, hb, -⟩ := hβ t
  have hc : ∀ U : P.A.left.Opens, ∃ e : ℂ →+* Γ(P.A.left, U), ∀ x, constFn P.A.hom U x = e x := fun U =>
    ⟨((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ P.A.hom.appLE ⊤ U (fun _ _ => trivial)).hom, fun _ => rfl⟩
  have ha0 : a i₀ ≠ 0 := by
    intro h0
    apply hθ
    funext z
    have hm : (u.ex z).left (default : PrimeSpectrum ℂ) ∈ (⊤ : P.A.left.Opens) := trivial
    rw [← P.isLB.cover] at hm
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
    have hi₁ : ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i := (top_le_preimage_iff_mem _ _).2 hi
    have hi₂ : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow P.L 1).U (fun _ => i) :=
      (top_le_preimage_iff_mem _ _).2 (Set.mem_iInter.2 fun _ => hi)
    have e := hs (fun _ => i) z hi₂
    obtain ⟨c, hc'⟩ := hc ((lbPow P.L 1).U (fun _ => i))
    have e0 := (ha (fun _ => i)).trans (su _)
    rw [h0, hc', map_zero, zero_mul] at e0
    have e1 := e.symm.trans ((congrArg (valAt' _ _) e0).trans (valAt'_zero _ _))
    rw [pow_one] at e1
    exact (mul_eq_zero.1 e1).resolve_right (u.fr_ne i z hi₁)
  refine ⟨b i₀ / a i₀, fun j => ?_⟩
  obtain ⟨c, hc'⟩ := hc ((lbPow P.L 1).U j)
  rw [ha, hb, su, su, hc', hc', hc', ← _root_.mul_assoc, ← map_mul, div_mul_cancel₀ _ ha0]

theorem exists_isGenSec_of_isThetaFn : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin P.g → ℂ) → ℂ) (T : Over (Sp ℂ)) [IsIso T.hom] (p : 𝟙_ (Over (Sp ℂ)) ⟶ T), u.IsAH Hm χ → u.IsThetaFn Hm χ 1 θ → θ ≠ 0 → ∃ th : LB.Sec (Out.LPow P.A P.L 1 T), Out.IsGenSec P.A P.L 1 th ∧ (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L 1 T).U j) (th.f j) = θ z * u.fr (j 0) z ^ (1 : ℤ)) := by
  intro hL hL2 hG hU P u Hm χ θ T _ p hAH hθ hne
  obtain ⟨-, -, -, -, -, -, -, hsec, -⟩ := GlobalTheory.T.appellHumbert_uniformisation_riemannForm hL hL2 hG hU P u Hm χ hAH
  obtain ⟨s, hs, -⟩ := (hsec 1).2 θ hθ
  have hT : ∀ {X : Over (Sp ℂ)} (f g : X ⟶ T), f = g := fun f g =>
    Over.OverMorphism.ext ((cancel_mono T.hom).1 ((Over.w f).trans (Over.w g).symm))
  let ρ : P.A ⟶ T ⊗ P.A := lift (toUnit _ ≫ p) (𝟙 _)
  have r₂ : ρ ≫ snd T P.A = 𝟙 _ := lift_snd _ _
  have r₃ : snd T P.A ≫ ρ = 𝟙 _ :=
    CartesianMonoidalCategory.hom_ext _ _ (hT _ _) (by rw [Category.assoc, r₂, Category.comp_id, Category.id_comp])
  have ρ₂ : ρ.left ≫ (snd T P.A).left = 𝟙 _ := congrArg (fun q => q.left) r₂
  have ρ₃ : (snd T P.A).left ≫ ρ.left = 𝟙 _ := congrArg (fun q => q.left) r₃
  have ρ₁ : ρ.left ≫ (fst T P.A).left ≫ T.hom = P.A.hom := Over.w (ρ ≫ fst T P.A)
  haveI : IsIso ρ.left := ⟨_, ρ₂, ρ₃⟩
  obtain ⟨th, hth⟩ := PowSec.down_surjective P.L (snd T P.A).left ρ.left ρ₂ ((1 : ℕ) : ℤ) s
  refine ⟨th, fun t => ?_, fun j z hz => ?_⟩
  · obtain ⟨a, ha⟩ := exists_const_mul_of_isFnPow_ne_zero hL.globalSectionsRank P u θ hne s hs
      (PowSec.down P.L (snd T P.A).left ρ.left ρ₂ ((1 : ℕ) : ℤ) t)
    refine ⟨T.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a), fun j => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j 0, funext fun q => by rw [Subsingleton.elim q 0]⟩
    have hch := PowSec.chart_eq P.L (snd T P.A).left ρ.left ρ₂ (fun _ => k)
    refine PowSec.appLE_injective ρ.left _ _ hch ?_
    refine (ha (fun _ => k)).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) (map_mul (ρ.left.appLE _ _ hch.le).hom _ _).symm)
    · have h0 : (T.hom.appTop ≫ (fst T P.A).left.appTop ≫ (T ⊗ P.A).left.presheaf.map (homOfLE le_top).op) =
          ((fst T P.A).left ≫ T.hom).appLE ⊤ (LB.wchart P.L (fun _ : Fin 1 => (snd T P.A).left) (fun _ => k))
            (fun _ _ => trivial) := by
        rw [← Category.assoc, ← Scheme.Hom.comp_appTop]; rfl
      have h1 := (Scheme.Hom.appLE_comp_appLE ρ.left ((fst T P.A).left ≫ T.hom) ⊤ _ _ (fun _ _ => trivial)
        hch.le).trans (PowSec.appLE_congr ρ₁ ⊤ _ _ (fun _ _ => trivial))
      rw [← h0] at h1
      exact (congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) h1).symm
    · rw [← hth]; rfl
  · obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j 0, funext fun q => by rw [Subsingleton.elim q 0]⟩
    have hch := PowSec.chart_eq P.L (snd T P.A).left ρ.left ρ₂ (fun _ => k)
    have hz₂ : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow P.L 1).U (fun _ => k) :=
      (top_le_preimage_iff_mem _ _).2 (Set.mem_iInter.2 fun _ => (top_le_preimage_iff_mem _ _).1 hz)
    have e := hs (fun _ => k) z hz₂
    have e₁ : lift p (u.ex z) = u.ex z ≫ ρ :=
      CartesianMonoidalCategory.hom_ext _ _ (hT _ _) (by rw [Category.assoc, r₂, Category.comp_id, lift_snd])
    have e₂ := valAt'_appLE (u.ex z).left ρ.left _ _ hch.le (th.f (fun _ => k)) hz₂
    rw [e₁, zpow_one]
    rw [← hth, pow_one] at e
    exact e₂.symm.trans e

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_mulPull_gen_over (H : Out.MulPullSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S)
    (T : Over S) (N : ℕ) :
    ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ N).left] ![(N : ℤ) ^ 2, -1]),
      α.IsGen := by
  obtain ⟨α₀, hα₀⟩ := H _ P N
  have e₁ : (snd T P.A).left ≫ (Out.mulA P.A N).left = (snd T P.A ^ N).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨α, hα, -⟩ := exists_gen P.isLB (φ' := ![(snd T P.A).left, (snd T P.A ^ N).left])
    (ε' := ![(N : ℤ) ^ 2, -1])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ ((N : ℤ) ^ 2)) (Category.comp_id _)
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen P.L ![𝟙 P.A.left, (Out.mulA P.A N).left] ![(N : ℤ) ^ 2, -1] α₀ (snd T P.A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  exact ⟨α, hα⟩

theorem exists_twistPull_mul_fn : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (N : ℕ) (θ : (Fin P.g → ℂ) → ℂ) (T : Over (Sp ℂ)) [IsIso T.hom] (p : 𝟙_ (Over (Sp ℂ)) ⟶ T) (th : LB.Sec (Out.LPow P.A P.L 1 T)), u.IsAH Hm χ → Odd N → (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L 1 T).U j) (th.f j) = θ z * u.fr (j 0) z ^ (1 : ℤ)) → ∃ (s1 : LB.Sec (Out.LPow P.A P.L ((N : ℤ) ^ 2) T)) (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ N).left] ![(N : ℤ) ^ 2, -1])) (c : ℂ), c ≠ 0 ∧ α.IsGen ∧ Out.IsTwistPull P.A P.L (Out.mulT P.A T N) (snd T P.A ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α th s1 ∧ (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L ((N : ℤ) ^ 2) T).U j) (s1.f j) = c * θ ((N : ℂ) • z) * u.fr (j 0) z ^ (((N : ℤ) ^ 2) : ℤ)) := by
  intro hLaw _ _ _ P u Hm χ N θ T _ p th hAH _ hth
  have hL := P.isLB
  obtain ⟨α, hα⟩ := exists_mulPull_gen_over hLaw.mulPull P T N
  obtain ⟨s1, hs1⟩ := ThetaPtExist.exists_isTwistPull hL (Out.mulT P.A T N) (snd T P.A ^ N) (lift_snd _ _)
    ((N : ℤ) ^ 2) 1 α hα th
  obtain ⟨c, hc0, -, hc, -⟩ := (ThetaFn.pull_analytic_at hL hAH (ψ := Out.mulT P.A T N) (p := p)
    (m := snd T P.A ^ N) (lift_snd _ _) (Φ := (N : ℂ) • LinearMap.id) (fun z => by
      rw [LinearMap.smul_apply, LinearMap.id_apply, ThetaFn.exAt_mulT]) (a := (N : ℤ) ^ 2) (b := 1) hα).2
  have h1 : ThetaFn.IsFnAt u p 1 th θ := fun j z hj =>
    hth j z ((ThetaFn.exAt_mem_chart_iff u p 1 j z).1 hj)
  have h2 := ThetaFn.isFnAt_fnAt u p hL ((N : ℤ) ^ 2) s1
  refine ⟨s1, α, c, hc0, hα, hs1, fun j z hj => ?_⟩
  refine (h2 j z ((ThetaFn.exAt_mem_chart_iff u p _ j z).2 hj)).trans ?_
  rw [hc th s1 θ _ hs1 h1 h2 z]
  rfl

end GlobalTheory
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SymLiftFrame

open ThetaFn CubeValues SymmetricSemicharacter AppellHumbertTrivial ReciprocityTheory.ChartRestriction.G.Out

section Values

variable {X Y Y' : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

def cval {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp ℂ ⟶ Y)
    (J : (Sp ℂ ⟶ X) → L.ι) : ℂ :=
  valAt' r (LB.wchart L φ fun k => J (r ≫ φ k)) (t.s fun k => J (r ≫ φ k)).val

private theorem valAt'_presheaf_map_homOfLE {Z : Scheme.{0}} (x : Sp ℂ ⟶ Z) {U V : Z.Opens} (hVU : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(Z, U)) :
    valAt' x V (Z.presheaf.map (homOfLE hVU).op f) = valAt' x U f := by
  unfold valAt'
  rw [dif_pos h, dif_pos (h.trans fun p hp => hVU hp)]
  unfold valAt
  congr 1
  rw [← Scheme.Hom.map_appLE x h (homOfLE hVU).op]
  rfl

private theorem valAt'_mul_moduli {Z : Scheme.{0}} (x : Sp ℂ ⟶ Z) (U : Z.Opens) (f f' : Γ(Z, U)) :
    valAt' x U (f * f') = valAt' x U f * valAt' x U f' := by
  unfold valAt'
  split_ifs with h
  · unfold valAt
    rw [map_mul, map_mul]
  · rw [zero_mul]

private theorem valAt'_units_inv' {Z : Scheme.{0}} (x : Sp ℂ ⟶ Z) (U : Z.Opens) (f : Γ(Z, U)ˣ) :
    valAt' x U ↑f⁻¹ = (valAt' x U ↑f)⁻¹ := by
  unfold valAt'
  split_ifs with h
  · refine eq_inv_of_mul_eq_one_left ?_
    unfold valAt
    rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
  · rw [inv_zero]

private theorem valAt'_app_eq_valAt'_comp' {Z Z' : Scheme.{0}} (x : Sp ℂ ⟶ Z') (q : Z' ⟶ Z) (U : Z.Opens)
    (h : ⊤ ≤ (x ≫ q) ⁻¹ᵁ U) (f : Γ(Z, U)) :
    valAt' x (q ⁻¹ᵁ U) (q.app U f) = valAt' (x ≫ q) U f := by
  unfold valAt'
  rw [dif_pos h, dif_pos (show ⊤ ≤ x ⁻¹ᵁ q ⁻¹ᵁ U from h)]
  unfold valAt
  congr 1

private theorem valAt'_one_moduli {Z : Scheme.{0}} (x : Sp ℂ ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    valAt' x U 1 = 1 := by
  unfold valAt'
  rw [dif_pos h]
  unfold valAt
  rw [map_one, map_one]

private theorem valAt'_finset_prod {Z : Scheme.{0}} {I : Type} (x : Sp ℂ ⟶ Z) (U : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Finset I) (f : I → Γ(Z, U)) :
    valAt' x U (∏ i ∈ s, f i) = ∏ i ∈ s, valAt' x U (f i) := by
  unfold valAt'
  simp only [dif_pos h]
  unfold valAt
  rw [map_prod, map_prod]

theorem cval_of {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp ℂ ⟶ Y)
    (J : (Sp ℂ ⟶ X) → L.ι) (j : K → L.ι) (h : ∀ k, J (r ≫ φ k) = j k) :
    cval t r J = valAt' r (LB.wchart L φ j) (t.s j).val := by
  have e : (fun k => J (r ≫ φ k)) = j := funext h
  subst e
  rfl

variable {J : (Sp ℂ ⟶ X) → L.ι} (hJ : ∀ ψ : Sp ℂ ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ))
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
include hJ

theorem mem_chart (φ : K → (Y ⟶ X)) (r : Sp ℂ ⟶ Y) :
    ⊤ ≤ r ⁻¹ᵁ LB.wchart L φ fun k => J (r ≫ φ k) := by
  intro p _
  refine Set.mem_iInter.2 fun k => ?_
  have hk := hJ (r ≫ φ k) (show p ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  simpa using hk

theorem cval_ne_zero (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp ℂ ⟶ Y) : cval t r J ≠ 0 := by
  intro h0
  have h1 := valAt'_mul_moduli r ((L.LinComb φ ε).U fun k => J (r ≫ φ k))
    ((t.s fun k => J (r ≫ φ k))⁻¹).val (t.s fun k => J (r ≫ φ k)).val
  rw [Units.inv_mul] at h1
  have h2 : valAt' r ((L.LinComb φ ε).U fun k => J (r ≫ φ k)) (t.s fun k => J (r ≫ φ k)).val = 0 := h0
  rw [h2, mul_zero] at h1
  exact one_ne_zero ((valAt'_one_moduli r _ (mem_chart hJ φ r)).symm.trans h1)

theorem cval_mul (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (r : Sp ℂ ⟶ Y) : cval (LB.mulGen L φ ε φ' ε' t t') r J = cval t r J * cval t' r J := by
  unfold cval LB.mulGen
  dsimp only
  unfold res
  rw [Units.val_mul, valAt'_mul_moduli, Units.coe_map, Units.coe_map]
  exact congrArg₂ (· * ·) (valAt'_presheaf_map_homOfLE _ _ (mem_chart hJ _ r) _) (valAt'_presheaf_map_homOfLE _ _ (mem_chart hJ _ r) _)

theorem cval_inv (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp ℂ ⟶ Y) :
    cval (LB.invGen L φ ε t) r J = (cval t r J)⁻¹ := by
  unfold cval LB.invGen
  exact valAt'_units_inv' _ _ _

theorem cval_pull (t : LB.Gen (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (r : Sp ℂ ⟶ Y') :
    cval (LB.pullGen L φ ε t h) r J = cval t (r ≫ h) J := by
  rw [cval_of t (r ≫ h) J (fun k => J (r ≫ h ≫ φ k)) (fun k => congrArg J (Category.assoc r h (φ k)))]
  unfold cval LB.pullGen pullU res
  dsimp only
  rw [Units.coe_map, Units.coe_map]
  exact (valAt'_presheaf_map_homOfLE _ _ (mem_chart hJ _ r) _).trans (valAt'_app_eq_valAt'_comp' r h _ (mem_chart hJ φ (r ≫ h)) _)

theorem cval_corr_one {t : LB.Gen (LB.LinComb L φ ε)}
    (h : LB.Gen.Corr L φ ε _ _ t (LB.oneGen L)) (r : Sp ℂ ⟶ Y) : cval t r J = 1 := by
  have e := h (fun k => J (r ≫ φ k)) PEmpty.elim (fun k₁ k₂ hk => by simp only [hk])
    (fun k _ _ => k.elim) (fun _ k' _ => k'.elim)
  unfold res LB.oneGen at e
  have h0 : ⊤ ≤ r ⁻¹ᵁ L.wchart (PEmpty.elim : PEmpty.{1} → (Y ⟶ X)) PEmpty.elim := by
    intro p _
    exact Set.mem_iInter.2 fun k => k.elim
  have hV : ⊤ ≤ r ⁻¹ᵁ ((L.wchart φ fun k => J (r ≫ φ k)) ⊓
      L.wchart (PEmpty.elim : PEmpty.{1} → (Y ⟶ X)) PEmpty.elim) := by
    intro p hp
    exact ⟨mem_chart hJ φ r hp, h0 hp⟩
  have e3 := congrArg (valAt' r _) (congrArg Units.val e)
  refine ((valAt'_presheaf_map_homOfLE r inf_le_left hV _).symm.trans e3).trans ?_
  refine (valAt'_presheaf_map_homOfLE r inf_le_right hV _).trans ?_
  exact valAt'_one_moduli r _ h0

end Values

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g}
  {T : Over (Sp ℂ)} {p : 𝟙_ (Over (Sp ℂ)) ⟶ T} {J : (Sp ℂ ⟶ A.left) → L.ι}
  (hJ : ∀ ψ : Sp ℂ ⟶ A.left, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ))

include hJ in

theorem cval_powGen {k : ℤ} (θ : ThetaGrp A L k T) (n : ℕ) (r : Sp ℂ ⟶ (T ⊗ A).left) :
    cval (powGen A L k θ n) r J =
      ∏ i ∈ Finset.range n, cval (L := L) θ.φ (r ≫ (translT A (θ.pt ^ i)).left) J := by
  rw [← Fin.prod_univ_eq_prod_range]
  unfold powGen
  conv_lhs => unfold cval
  dsimp only
  rw [Units.coe_prod]
  refine (valAt'_finset_prod r _ (mem_chart hJ _ r) _ _).trans (Finset.prod_congr rfl fun i _ => ?_)
  unfold res
  refine (valAt'_presheaf_map_homOfLE r _ (mem_chart hJ _ r) _).trans ?_
  exact cval_pull hJ θ.φ (translT A (θ.pt ^ (i : ℕ))).left r

include hJ in

theorem cval_symGen {k : ℤ} (θ : ThetaGrp A L k T) (nu : LB.Gen (negLB A L k T))
    (r : Sp ℂ ⟶ (T ⊗ A).left) :
    cval (symGen A L k θ nu) r J =
      cval (L := L) θ.φ (r ≫ (translT A θ.pt⁻¹).left) J * cval (L := L) nu r J *
        (cval (L := L) θ.φ (r ≫ (negT A T).left) J *
          (cval (L := L) nu (r ≫ (translT A θ.pt⁻¹).left) J)⁻¹) := by
  unfold symGen
  rw [cval_mul hJ, cval_mul hJ, cval_mul hJ _ nu, cval_pull hJ θ.φ, cval_pull hJ θ.φ, cval_inv hJ,
    cval_pull hJ nu]

theorem cval_two {m : T ⊗ A ⟶ A} {ε : Fin 2 → ℤ}
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ε)) {z w : Fin g → ℂ}
    (h : exAt u p z ≫ m.left = (u.ex w).left) :
    cval α (exAt u p z) J = valAt' (exAt u p z) (LB.wchart L ![(snd T A).left, m.left]
      ![J (u.ex z).left, J (u.ex w).left]) (α.s ![J (u.ex z).left, J (u.ex w).left]).val := by
  refine cval_of α _ J _ fun i => ?_
  fin_cases i
  · show J ((lift p (u.ex z)).left ≫ (snd T A).left) = J (u.ex z).left
    rw [← Over.comp_left, lift_snd]
  · exact congrArg J h

variable {Hm : Matrix (Fin g) (Fin g) ℂ} {k : ℤ} {Θ : ThetaGrp A L k T} {x : Fin g → ℂ} {c : ℂ}

include hJ in
theorem cval_theta (hc : HasAnConst u p Hm Θ x c) (z : Fin g → ℂ) :
    cval (L := L) Θ.φ (exAt u p z) J * u.fr (J (u.ex (z + x)).left) (z + x) ^ k =
      c * fockFactor Hm k x z * u.fr (J (u.ex z).left) z ^ k := by
  rw [cval_of Θ.φ (exAt u p z) J ![J (u.ex z).left, J (u.ex (z + x)).left] (fun i => ?_)]
  · exact hc.2 _ z (hJ _) (hJ _)
  · fin_cases i
    · show J ((lift p (u.ex z)).left ≫ (snd T A).left) = J (u.ex z).left
      rw [← Over.comp_left, lift_snd]
    · exact congrArg J (exAt_translPt u hc.1 z)

theorem exists_choice (hL : L.IsLB) :
    ∃ J : (Sp ℂ ⟶ A.left) → L.ι, ∀ ψ : Sp ℂ ⟶ A.left, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ) := by
  have hpt : ∀ a b : Sp ℂ, a = b := fun a b =>
    PrimeSpectrum.ext (((Ideal.eq_bot_or_top a.asIdeal).resolve_right a.isPrime.ne_top).trans
      ((Ideal.eq_bot_or_top b.asIdeal).resolve_right b.isPrime.ne_top).symm)
  have key : ∀ ψ : Sp ℂ ⟶ A.left, ∃ i, ⊤ ≤ ψ ⁻¹ᵁ L.U i := by
    intro ψ
    obtain ⟨p0⟩ : Nonempty (PrimeSpectrum ℂ) := inferInstance
    have h0 : ψ p0 ∈ (⨆ i, L.U i) := by
      rw [hL.cover]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h0
    exact ⟨i, fun p _ => by rw [hpt p p0]; exact hi⟩
  choose J hJ using key
  exact ⟨J, hJ⟩

theorem pow_mul_eq_one (hL : L.IsLB) {χ : u.Λ → ℂ} (hAH : u.IsAH Hm χ)
    (hc : HasAnConst u p Hm Θ x c) {n : ℕ} {l : u.Λ} (hl : (n : ℂ) • x = l)
    (h : LB.Gen.Corr L _ _ _ _ (powGen A L k Θ n) (LB.oneGen L)) : c ^ n * χ l ^ k = 1 := by
  obtain ⟨J, hJ⟩ := exists_choice hL
  have hex0 : u.ex 0 = 1 := (u.ker 0).2 (zero_mem _)
  have hpt : ∀ i : ℕ, p ≫ Θ.pt ^ i = u.ex ((i : ℂ) • x) := fun i => by
    rw [MonObj.comp_pow, hc.1, ex_natCast_smul]
  have key : ∀ m : ℕ, (∏ i ∈ Finset.range m, cval (L := L) Θ.φ (exAt u p ((i : ℂ) • x)) J) *
      u.fr (J (u.ex ((m : ℂ) • x)).left) ((m : ℂ) • x) ^ k =
      c ^ m * Complex.exp (-((k : ℂ) * (Real.pi : ℂ) * ((m : ℂ) ^ 2 / 2) * hermForm Hm x x)) *
        u.fr (J (u.ex 0).left) 0 ^ k := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have t := cval_theta hJ hc ((m : ℂ) • x)
      have hm1 : (m : ℂ) • x + x = ((m + 1 : ℕ) : ℂ) • x := by
        push_cast
        rw [add_smul, one_smul]
      rw [hm1] at t
      have hE : fockFactor Hm k x ((m : ℂ) • x) *
          Complex.exp (-((k : ℂ) * (Real.pi : ℂ) * ((m : ℂ) ^ 2 / 2) * hermForm Hm x x)) =
          Complex.exp (-((k : ℂ) * (Real.pi : ℂ) * (((m + 1 : ℕ) : ℂ) ^ 2 / 2) * hermForm Hm x x)) := by
        unfold fockFactor
        rw [← Complex.exp_add, hermForm_smul_left]
        congr 1
        push_cast
        ring
      rw [Finset.prod_range_succ]
      linear_combination (∏ i ∈ Finset.range m, cval (L := L) Θ.φ (exAt u p ((i : ℂ) • x)) J) * t +
        (c * fockFactor Hm k x ((m : ℂ) • x)) * ih +
        (c ^ (m + 1) * u.fr (J (u.ex 0).left) 0 ^ k) * hE
  have hprod : ∏ i ∈ Finset.range n, cval (L := L) Θ.φ (exAt u p ((i : ℂ) • x)) J = 1 := by
    have h1 := cval_corr_one hJ h (exAt u p 0)
    rw [cval_powGen hJ Θ n] at h1
    refine Eq.trans (Finset.prod_congr rfl fun i _ => ?_) h1
    rw [exAt_translT u (hpt i) 0, zero_add]
  have hl1 : u.ex (l : Fin g → ℂ) = u.ex 0 := by
    rw [hex0]
    exact (u.ker _).2 l.2
  have hk := key n
  rw [hprod, _root_.one_mul, hl, hl1] at hk
  have ha : u.fr (J (u.ex 0).left) 0 = χ l *
      Complex.exp ((Real.pi : ℂ) * hermForm Hm 0 l + (Real.pi : ℂ) / 2 * hermForm Hm l l) *
        u.fr (J (u.ex 0).left) (l : Fin g → ℂ) := by
    have := hAH.2.2.2 l (J (u.ex 0).left) 0 (hJ _)
    rw [zero_add] at this
    exact this
  have hak := congrArg (· ^ k) ha
  rw [mul_zpow, mul_zpow] at hak
  have h0 : hermForm Hm 0 (l : Fin g → ℂ) = 0 := zero_dotProduct _
  have hexp : Complex.exp ((Real.pi : ℂ) * hermForm Hm 0 l + (Real.pi : ℂ) / 2 * hermForm Hm l l) ^ k *
      Complex.exp (-((k : ℂ) * (Real.pi : ℂ) * ((n : ℂ) ^ 2 / 2) * hermForm Hm x x)) = 1 := by
    rw [← Complex.exp_int_mul, ← Complex.exp_add, h0, ← hl, hermForm_smul_left, hermForm_smul_right,
      star_natCast, ← Complex.exp_zero]
    congr 1
    ring
  have hfr0 : u.fr (J (u.ex 0).left) 0 ^ k ≠ 0 := zpow_ne_zero _ (u.fr_ne _ _ (hJ _))
  apply mul_right_cancel₀ hfr0
  linear_combination (-1 : ℂ) * hak -
    (χ l ^ k * Complex.exp ((Real.pi : ℂ) * hermForm Hm 0 l + (Real.pi : ℂ) / 2 * hermForm Hm l l) ^ k) * hk -
    (χ l ^ k * c ^ n * u.fr (J (u.ex 0).left) 0 ^ k) * hexp

theorem sq_eq_one (hL : L.IsLB) {χ : u.Λ → ℂ} (hAH : u.IsAH Hm χ)
    (hc : HasAnConst u p Hm Θ x c) {nu : LB.Gen (negLB A L k T)} (hnu : nu.IsGen)
    (h : LB.Gen.Corr L _ _ _ _ (symGen A L k Θ nu) (LB.oneGen L)) : c ^ 2 = 1 := by
  obtain ⟨J, hJ⟩ := exists_choice hL
  have hex0 : u.ex 0 = 1 := (u.ker 0).2 (zero_mem _)
  have hneg : ∀ z, u.ex (-z) = u.ex z ≫ ι := fun z => by
    rw [GrpObj.inv_eq_inv, GrpObj.comp_inv, Category.comp_id]
    refine (eq_inv_of_mul_eq_one_right ?_)
    rw [← u.ex_add, add_neg_cancel, hex0]
  have hxi : p ≫ Θ.pt⁻¹ = u.ex (-x) := by
    rw [GrpObj.comp_inv, hc.1, hneg, GrpObj.inv_eq_inv, GrpObj.comp_inv, Category.comp_id]
  have e2 : exAt u p 0 ≫ (negT A T).left = exAt u p 0 := by
    unfold negT exAt
    rw [← Over.comp_left, comp_lift, lift_fst, ← Category.assoc, lift_snd, ← hneg, neg_zero]
  have hΦ : ∀ z, exAt u p z ≫ (snd T A ≫ ι).left = (u.ex (-z)).left := fun z =>
    exAt_snd_comp p (hneg z)
  obtain ⟨-, -, cν, hcν0, hcν⟩ := exists_isPullConst hL hAH (Φ := -LinearMap.id)
    (fun z => by simpa only [LinearMap.neg_apply, LinearMap.id_apply] using hΦ z) (a := k) (b := k) hnu
  have hN : ∀ z, cval (L := L) nu (exAt u p z) J * u.fr (J (u.ex (-z)).left) (-z) ^ k =
      cν * u.fr (J (u.ex z).left) z ^ k := fun z => by
    rw [cval_of nu _ J ![J (u.ex z).left, J (u.ex (-z)).left] (fun i => ?_)]
    · exact hcν _ z ((exAt_mem_pairChart_iff (hΦ z) _).2 ⟨hJ _, hJ _⟩)
    · fin_cases i
      · show J ((lift p (u.ex z)).left ≫ (snd T A).left) = J (u.ex z).left
        rw [← Over.comp_left, lift_snd]
      · exact congrArg J (hΦ z)
  have hs := cval_corr_one hJ h (exAt u p 0)
  rw [cval_symGen hJ Θ nu, exAt_translT u hxi 0, zero_add, e2] at hs
  have t1 := cval_theta hJ hc (-x)
  have t2 := cval_theta hJ hc 0
  have p1 := hN 0
  have p2 := hN (-x)
  rw [neg_add_cancel] at t1
  rw [zero_add] at t2
  rw [neg_zero] at p1
  rw [neg_neg] at p2
  have hf : fockFactor Hm k x (-x) * fockFactor Hm k x 0 = 1 := by
    unfold fockFactor hermForm
    rw [← Complex.exp_add, neg_dotProduct, zero_dotProduct, ← Complex.exp_zero]
    congr 1
    ring
  have hF0 : u.fr (J (u.ex 0).left) 0 ^ k ≠ 0 := zpow_ne_zero _ (u.fr_ne _ _ (hJ _))
  have hFm : u.fr (J (u.ex (-x)).left) (-x) ^ k ≠ 0 := zpow_ne_zero _ (u.fr_ne _ _ (hJ _))
  have hn2 : cval (L := L) nu (exAt u p (-x)) J ≠ 0 := cval_ne_zero hJ nu _
  have hn1 : cval (L := L) nu (exAt u p 0) J = cν := mul_right_cancel₀ hF0 p1
  rw [hn1] at hs
  have e2' : cval (L := L) Θ.φ (exAt u p (-x)) J * cval (L := L) Θ.φ (exAt u p 0) J * cν =
      cval (L := L) nu (exAt u p (-x)) J := by
    have hi := mul_inv_cancel₀ hn2
    linear_combination (cval (L := L) nu (exAt u p (-x)) J) * hs -
      (cval (L := L) Θ.φ (exAt u p (-x)) J * cν * cval (L := L) Θ.φ (exAt u p 0) J) * hi
  apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero hFm hF0) hcν0)
  linear_combination (-cν) * ((cval (L := L) Θ.φ (exAt u p 0) J * u.fr (J (u.ex x).left) x ^ k) * t1 +
      (c * fockFactor Hm k x (-x) * u.fr (J (u.ex (-x)).left) (-x) ^ k) * t2 +
      (c ^ 2 * u.fr (J (u.ex (-x)).left) (-x) ^ k * u.fr (J (u.ex 0).left) 0 ^ k) * hf) +
    (u.fr (J (u.ex 0).left) 0 ^ k * u.fr (J (u.ex x).left) x ^ k) * e2' + u.fr (J (u.ex 0).left) 0 ^ k * p2

end GlobalTheory.SymLiftFrame

open GlobalTheory.SymLiftFrame GlobalTheory.ThetaFn GlobalTheory.AppellHumbertTrivial in

theorem GlobalTheory.symLift_act_in_frame : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (N : ℕ) (l : u.Λ) (f : (Fin P.g → ℂ) → ℂ) (T : Over (Sp ℂ)) [IsIso T.hom] (p : 𝟙_ (Over (Sp ℂ)) ⟶ T) (x : T ⟶ P.A) (U : Out.ThetaGrp P.A P.L ((N : ℤ) ^ 2) T) (s s' : LB.Sec (Out.LPow P.A P.L ((N : ℤ) ^ 2) T)), u.IsAH Hm χ → Odd N → p ≫ x = u.ex (((N : ℂ) ^ 2)⁻¹ • (l : Fin P.g → ℂ)) → Out.SymLift P.A P.L ((N : ℤ) ^ 2) (N ^ 2) x U → Out.IsActOf P.A P.L ((N : ℤ) ^ 2) U s s' → (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L ((N : ℤ) ^ 2) T).U j) (s.f j) = f z * u.fr (j 0) z ^ (((N : ℤ) ^ 2) : ℤ)) → (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L ((N : ℤ) ^ 2) T).U j) (s'.f j) = (χ l * Complex.exp (-(Real.pi / 2 / (N : ℂ) ^ 2) * hermForm Hm l l - Real.pi * hermForm Hm z l) * f (z + ((N : ℂ) ^ 2)⁻¹ • (l : Fin P.g → ℂ))) * u.fr (j 0) z ^ (((N : ℤ) ^ 2) : ℤ)) := by
  intro _ _ _ _ P u Hm χ N l f T _ p x U s s' hAH hN hx hS hAct hs j z hz
  obtain ⟨J, hJ⟩ := exists_choice P.isLB
  obtain ⟨hpteq, hpow, nu, hnu, hsym⟩ := hS
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.pos_of_ne_zero (by rintro rfl; exact absurd hN (by decide))).ne'
  set x0 : Fin P.g → ℂ := ((N : ℂ) ^ 2)⁻¹ • (l : Fin P.g → ℂ) with hx0
  have hpt0 : p ≫ U.pt = u.ex x0 := by rw [hpteq, hx]
  obtain ⟨c, hc⟩ := (exists_hasAnConst P.isLB hAH hpt0).2
  have hl' : ((N ^ 2 : ℕ) : ℂ) • x0 = l := by
    rw [hx0, smul_smul]
    push_cast
    rw [mul_inv_cancel₀ (pow_ne_zero 2 hN0), one_smul]
  have hpowc := pow_mul_eq_one P.isLB hAH hc hl' hpow
  have hsq := sq_eq_one P.isLB hAH hc hnu hsym
  have hχ := GlobalTheory.semicharacter_sq_eq_one_of_symmetric P u Hm χ hAH l
  obtain ⟨m, hm⟩ : Odd (N ^ 2) := hN.pow
  rw [show ((N : ℤ) ^ 2) = ((N ^ 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, hm, pow_succ, pow_succ,
    pow_mul, pow_mul, hsq, hχ] at hpowc
  simp only [one_pow, _root_.one_mul] at hpowc
  have hcχ : c = χ l := by linear_combination (χ l) * hpowc - c * hχ
  obtain ⟨j0, rfl⟩ : ∃ j0, j = fun _ => j0 := ⟨j 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  have hsnd : ∀ w, exAt u p w ≫ (snd T P.A).left = (u.ex w).left := fun w => by
    show (lift p (u.ex w)).left ≫ (snd T P.A).left = _
    rw [← Over.comp_left, lift_snd]
  have hW : ∀ w, ⊤ ≤ exAt u p w ⁻¹ᵁ
      LB.wchart P.L (fun _ : Fin 1 => (snd T P.A).left) (fun _ => J (u.ex w).left) := fun w => by
    have h1 := mem_chart hJ (fun _ : Fin 1 => (snd T P.A).left) (exAt u p w)
    simp only [hsnd] at h1
    exact h1
  have htr : exAt u p z ≫ (Out.translPt P.A U.pt).left = (u.ex (z + x0)).left := exAt_translPt u hpt0 z
  have hV : ⊤ ≤ exAt u p z ⁻¹ᵁ LB.wchart P.L ![(snd T P.A).left, (Out.translPt P.A U.pt).left]
      ![j0, J (u.ex (z + x0)).left] :=
    (exAt_mem_pairChart_iff htr _).2 ⟨hz, hJ _⟩
  have e := congrArg (valAt' (exAt u p z) _) (hAct ![j0, J (u.ex (z + x0)).left])
  have e2 : valAt' (exAt u p z) ((Out.LPow P.A P.L ((N : ℤ) ^ 2) T).U fun _ => j0) (s'.f fun _ => j0) =
      valAt' (exAt u p z) (LB.wchart P.L ![(snd T P.A).left, (Out.translPt P.A U.pt).left]
        ![j0, J (u.ex (z + x0)).left]) (U.φ.s ![j0, J (u.ex (z + x0)).left]).val *
      valAt' (exAt u p (z + x0)) ((Out.LPow P.A P.L ((N : ℤ) ^ 2) T).U fun _ => J (u.ex (z + x0)).left)
        (s.f fun _ => J (u.ex (z + x0)).left) := by
    refine (valAt'_presheaf_map_homOfLE _ _ hV _).symm.trans (e.trans ((valAt'_mul_moduli _ _ _ _).trans ?_))
    refine congrArg₂ (· * ·) rfl ?_
    refine (valAt'_presheaf_map_homOfLE _ _ hV _).trans ?_
    refine (valAt'_app_eq_valAt'_comp' _ _ _ ?_ _).trans ?_
    · rw [exAt_translT u hpt0 z]
      exact hW _
    · rw [exAt_translT u hpt0 z]
      rfl
  have hs' : valAt' (exAt u p (z + x0)) ((Out.LPow P.A P.L ((N : ℤ) ^ 2) T).U fun _ => J (u.ex (z + x0)).left)
      (s.f fun _ => J (u.ex (z + x0)).left) = f (z + x0) * u.fr (J (u.ex (z + x0)).left) (z + x0) ^ ((N : ℤ) ^ 2) :=
    hs _ _ (hJ _)
  have hc2 : valAt' (exAt u p z) (LB.wchart P.L ![(snd T P.A).left, (Out.translPt P.A U.pt).left]
        ![j0, J (u.ex (z + x0)).left]) (U.φ.s ![j0, J (u.ex (z + x0)).left]).val *
      u.fr (J (u.ex (z + x0)).left) (z + x0) ^ ((N : ℤ) ^ 2) =
      c * fockFactor Hm ((N : ℤ) ^ 2) x0 z * u.fr j0 z ^ ((N : ℤ) ^ 2) := hc.2 _ z hz (hJ _)
  have hfock : fockFactor Hm ((N : ℤ) ^ 2) x0 z =
      Complex.exp (-((Real.pi : ℂ) / 2 / (N : ℂ) ^ 2) * hermForm Hm l l - (Real.pi : ℂ) * hermForm Hm z l) := by
    unfold fockFactor
    congr 1
    rw [hx0]
    simp only [hermForm_smul_left, hermForm_smul_right, star_inv₀, star_pow, star_natCast]
    push_cast
    field_simp
    ring
  refine e2.trans ?_
  rw [hs']
  show _ = χ l * _ * f (z + x0) * u.fr j0 z ^ ((N : ℤ) ^ 2)
  linear_combination f (z + x0) * hc2 + (fockFactor Hm ((N : ℤ) ^ 2) x0 z * f (z + x0) *
    u.fr j0 z ^ ((N : ℤ) ^ 2)) * hcχ + (χ l * f (z + x0) * u.fr j0 z ^ ((N : ℤ) ^ 2)) * hfock
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.symmetricLift_torsionPoint_action_on_theta : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (N : ℕ) (l : u.Λ) (f : (Fin P.g → ℂ) → ℂ) (T : Over (Sp ℂ)) [IsIso T.hom] (p : 𝟙_ (Over (Sp ℂ)) ⟶ T) (x : T ⟶ P.A) (U : Out.ThetaGrp P.A P.L ((N : ℤ) ^ 2) T) (s s' : LB.Sec (Out.LPow P.A P.L ((N : ℤ) ^ 2) T)), u.IsAH Hm χ → Odd N → p ≫ x = u.ex (((N : ℂ) ^ 2)⁻¹ • (l : Fin P.g → ℂ)) → Out.SymLift P.A P.L ((N : ℤ) ^ 2) (N ^ 2) x U → Out.IsActOf P.A P.L ((N : ℤ) ^ 2) U s s' → (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L ((N : ℤ) ^ 2) T).U j) (s.f j) = f z * u.fr (j 0) z ^ (((N : ℤ) ^ 2) : ℤ)) → (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L ((N : ℤ) ^ 2) T).U j) (s'.f j) = (χ l * Complex.exp (-(Real.pi / 2 / (N : ℂ) ^ 2) * hermForm Hm l l - Real.pi * hermForm Hm z l) * f (z + ((N : ℂ) ^ 2)⁻¹ • (l : Fin P.g → ℂ))) * u.fr (j 0) z ^ (((N : ℤ) ^ 2) : ℤ)) := by
  first | exact @GlobalTheory.symLift_act_in_frame | exact GlobalTheory.symLift_act_in_frame | (intros; apply GlobalTheory.symLift_act_in_frame <;> assumption)
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.OriginValue

theorem eq_of_valAt'_eq_of_isIso {X : Scheme.{0}} (x : Sp ℂ ⟶ X) [IsIso x] (W : X.Opens) (f g : Γ(X, W))
    (h : ⊤ ≤ x ⁻¹ᵁ W → valAt' x W f = valAt' x W g) : f = g := by
  by_cases hW : ⊤ ≤ x ⁻¹ᵁ W
  · have h1 := h hW
    rw [valAt'_eq_valAt x hW, valAt'_eq_valAt x hW, valAt, valAt] at h1
    have h2 := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).1 h1
    have e : (⊤ : (Sp ℂ).Opens) = x ⁻¹ᵁ W := le_antisymm hW le_top
    have : IsIso (homOfLE hW) := ⟨⟨homOfLE le_top, rfl, rfl⟩⟩
    have : IsIso (x.appLE W ⊤ hW) := by
      unfold Scheme.Hom.appLE
      infer_instance
    exact (ConcreteCategory.bijective_of_isIso (x.appLE W ⊤ hW)).1 h2
  · have hb : W = ⊥ := by
      rw [top_le_preimage_iff_mem] at hW
      refine le_bot_iff.1 fun y hy => ?_
      obtain ⟨q, rfl⟩ := x.surjective y
      have : q = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
      subst this
      exact (hW hy).elim
    subst hb
    exact Subsingleton.elim _ _

def constFnHom {X : Scheme.{0}} (f : X ⟶ Sp ℂ) (U : X.Opens) : ℂ →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ f.appLE ⊤ U (fun _ _ => trivial)).hom

theorem top_le_preimage_wchart_one {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (x : Sp ℂ ⟶ Y) (j : Fin 1 → L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => φ) j) : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U (j 0) :=
  (top_le_preimage_comp x φ _).2 (top_le_preimage_mono x (LB.wchart_le L (fun _ : Fin 1 => φ) j 0) h)

theorem ex_zero {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) : u.ex 0 = 1 :=
  (u.ker 0).2 u.Λ.zero_mem

open Classical in

def unitOrOne (c : ℂ) : ℂˣ := if h : c ≠ 0 then Units.mk0 c h else 1

theorem unitOrOne_val {c : ℂ} (h : c ≠ 0) : (unitOrOne c : ℂ) = c := by
  rw [unitOrOne, dif_pos h]; rfl

theorem exists_gen_isValueAt_origin : ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (a : ℤ) (T : Over (Sp ℂ)) [IsIso T.hom] (p : 𝟙_ (Over (Sp ℂ)) ⟶ T), ∃ τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (1 : T ⟶ P.A).left) (fun _ => a)), τ.IsGen ∧ ∀ (s : LB.Sec (Out.LPow P.A P.L a T)) (f : (Fin P.g → ℂ) → ℂ), (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L a T).U j) (s.f j) = f z * u.fr (j 0) z ^ (a : ℤ)) → Out.IsValueAt P.A P.L a s 1 τ (constFn T.hom ⊤ (f 0)) := by
  intro P u a T _ p
  let x : Sp ℂ ⟶ T.left := p.left
  have hx : x ≫ T.hom = 𝟙 _ := Over.w p
  have : IsIso x := by
    have : x = inv T.hom := IsIso.eq_inv_of_inv_hom_id hx
    rw [this]; infer_instance
  have h1 : p ≫ (1 : T ⟶ P.A) = u.ex 0 := by
    rw [ex_zero, MonObj.comp_one]
  have h1' : x ≫ (1 : T ⟶ P.A).left = (u.ex 0).left := congrArg CommaMorphism.left h1
  have hch : ∀ j : Fin 1 → P.L.ι, ⊤ ≤ x ⁻¹ᵁ LB.wchart P.L (fun _ : Fin 1 => (1 : T ⟶ P.A).left) j →
      ⊤ ≤ (u.ex 0).left ⁻¹ᵁ P.L.U (j 0) := fun j h => by
    have := top_le_preimage_wchart_one P.L _ x j h
    rwa [h1'] at this
  let τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (1 : T ⟶ P.A).left) (fun _ => a)) :=
    ⟨fun j => Units.map (constFnHom T.hom _).toMonoidHom (unitOrOne (u.fr (j 0) 0) ^ a)⟩
  have hτ : ∀ j : Fin 1 → P.L.ι, ⊤ ≤ x ⁻¹ᵁ LB.wchart P.L (fun _ : Fin 1 => (1 : T ⟶ P.A).left) j →
      valAt' x (LB.wchart P.L (fun _ : Fin 1 => (1 : T ⟶ P.A).left) j) (τ.s j).val = u.fr (j 0) 0 ^ a := fun j h => by
    refine (valAt'_constFn x T.hom hx _ _ h).trans ?_
    rw [Units.val_zpow_eq_zpow_val, unitOrOne_val (u.fr_ne _ _ (hch j h))]
  refine ⟨τ, fun i j => ?_, fun s f hs j => ?_⟩
  · apply Units.ext
    refine eq_of_valAt'_eq_of_isIso x _ _ _ fun h => ?_
    obtain ⟨hi, hj⟩ := (top_le_preimage_inf x _ _).1 h
    rw [Units.val_mul, valAt'_mul]
    refine ((valAt'_res x inf_le_left _ h).trans (hτ i hi)).trans ?_
    have e2 := (valAt'_res x inf_le_right _ h).trans (hτ j hj)
    refine Eq.trans ?_ (congrArg _ e2.symm)
    have hij : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ (P.L.U (i 0) ⊓ P.L.U (j 0)) :=
      (top_le_preimage_inf (u.ex 0).left _ _).2 ⟨hch i hi, hch j hj⟩
    rw [u.fr_compat _ _ _ hij, mul_zpow]
    congr 1
    simp only [LB.LinComb, Fin.prod_univ_one]
    refine Eq.trans ?_ (valAt'_zpow x h _ a).symm
    congr 1
    refine Eq.trans ?_ (valAt'_res x _ _ h).symm
    refine Eq.trans ?_ (valAt'_comp x (1 : T ⟶ P.A).left (P.L.U (i 0) ⊓ P.L.U (j 0)) (P.L.g (i 0) (j 0)).val).symm
    rw [h1']
  · refine eq_of_valAt'_eq_of_isIso x _ _ _ fun h => ?_
    rw [valAt'_mul, hτ j h, valAt'_map x _ _ h, valAt'_map x _ _ h, valAt'_constFn x T.hom hx _ _ le_top]
    refine (valAt'_comp x _ _ _).trans ?_
    have h2 : p ≫ Out.ptSecT P.A (1 : T ⟶ P.A) = lift p (u.ex 0) := by
      rw [Out.ptSecT, comp_lift, Category.comp_id, h1]
    have h2' : x ≫ (Out.ptSecT P.A (1 : T ⟶ P.A)).left = (lift p (u.ex 0)).left := congrArg CommaMorphism.left h2
    rw [h2']
    exact hs j 0 (hch j h)

end GlobalTheory.OriginValue
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ThetaClassical

theorem constFn_mul {X : Scheme.{0}} (f : X ⟶ Sp ℂ) (U : X.Opens) (a b : ℂ) :
    constFn f U (a * b) = constFn f U a * constFn f U b := by
  unfold constFn
  rw [map_mul, map_mul]

theorem constFn_one {X : Scheme.{0}} (f : X ⟶ Sp ℂ) (U : X.Opens) : constFn f U 1 = 1 := by
  unfold constFn
  rw [map_one, map_one]

theorem constFn_top (a : ℂ) :
    (⊤ : (Sp ℂ).Opens).ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a) =
      constFn ((⊤ : (Sp ℂ).Opens).ι ≫ 𝟙 _) ⊤ a := by
  rw [Category.comp_id]
  exact congrArg (fun f : Γ(Sp ℂ, ⊤) ⟶ Γ((⊤ : (Sp ℂ).Opens).toScheme, (⊤ : (Sp ℂ).Opens).ι ⁻¹ᵁ ⊤) =>
    f.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a))
    (Scheme.Hom.appLE_eq_app (⊤ : (Sp ℂ).Opens).ι (U := ⊤)).symm

theorem isThetaPtOver (hL : Out.Laws) (hL2 : Out.Laws2) (hT : ThetaUnifAV) (P : Out.PolAV (Sp ℂ))
    (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ)
    (θ : (Fin P.g → ℂ) → ℂ) (N : ℕ) (T : Over (Sp ℂ)) [IsIso T.hom] (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
    {I : Type} (x : I → (T ⟶ P.A)) (l : I → u.Λ) (hN : Odd N) (hAH : u.IsAH Hm χ)
    (hθ : u.IsThetaFn Hm χ 1 θ) (h0 : θ ≠ 0)
    (hx : ∀ i, p ≫ x i = u.ex (((N : ℂ) ^ 2)⁻¹ • (l i : Fin P.g → ℂ)))
    (hU : ∀ i, ∃ U : Out.ThetaGrp P.A P.L ((N : ℤ) ^ 2) T,
      Out.SymLift P.A P.L ((N : ℤ) ^ 2) (N ^ 2) (x i) U) :
    Out.IsThetaPtOver P N x (fun i => constFn T.hom ⊤
      (χ (l i) * Complex.exp (-(Real.pi / 2 / (N : ℂ) ^ 2) * hermForm Hm (l i) (l i)) *
        θ ((N : ℂ)⁻¹ • (l i : Fin P.g → ℂ)))) := by
  have hC := GlobalTheory.Moduli.cube_of_isLB
  obtain ⟨th, hgen, hth⟩ := GlobalTheory.exists_isGenSec_of_isThetaFn hL hL2 hC hT P u Hm χ θ T p hAH hθ h0
  obtain ⟨s1, α, c, hc, hα, htw, hs1⟩ := GlobalTheory.exists_twistPull_mul_fn hL hL2 hC hT P u Hm χ N θ T p th hAH hN hth
  obtain ⟨τ, hτ, hval⟩ := GlobalTheory.OriginValue.exists_gen_isValueAt_origin P u ((N : ℤ) ^ 2) T p
  choose U hU using hU
  choose s2 hs2 using fun i => GlobalTheory.ThetaPtExist.exists_isTwistPull P.isLB (Out.translT P.A (U i).pt)
    (Out.translPt P.A (U i).pt) (lift_snd _ _) ((N : ℤ) ^ 2) ((N : ℤ) ^ 2) (U i).φ (U i).isGen s1
  have hact := fun i => GlobalTheory.T.symmetricLift_torsionPoint_action_on_theta hL hL2 hC hT P u Hm χ N (l i) (fun z => c * θ ((N : ℂ) • z)) T p
    (x i) (U i) s1 (s2 i) hAH hN (hx i) (hU i) (hs2 i) hs1
  have hv := fun i => hval (s2 i) (fun z => χ (l i) * Complex.exp (-(Real.pi / 2 / (N : ℂ) ^ 2) *
    hermForm Hm (l i) (l i) - Real.pi * hermForm Hm z (l i)) *
      (c * θ ((N : ℂ) • (z + ((N : ℂ) ^ 2)⁻¹ • (l i : Fin P.g → ℂ))))) (hact i)
  have hcu : IsUnit (constFn T.hom ⊤ c⁻¹) :=
    IsUnit.of_mul_eq_one (constFn T.hom ⊤ c) (by rw [← constFn_mul, inv_mul_cancel₀ hc, constFn_one])
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.pos.ne'
  refine ⟨th, s1, α, τ, U, s2, _, hcu.unit, hgen, hα, hτ, htw, hU, hs2, hv, fun i => ?_⟩
  refine Eq.trans (congrArg (constFn T.hom ⊤) ?_) (constFn_mul T.hom ⊤ c⁻¹ _)
  have e1 : hermForm Hm 0 (l i) = 0 := by simp [hermForm]
  have e2 : (N : ℂ) • (0 + ((N : ℂ) ^ 2)⁻¹ • (l i : Fin P.g → ℂ)) = (N : ℂ)⁻¹ • (l i : Fin P.g → ℂ) := by
    rw [zero_add, smul_smul]
    congr 1
    field_simp
  simp only [e1, e2, mul_zero, sub_zero]
  field_simp

theorem exists_symLift (hL : Out.Laws) (P : Out.PolAV (Sp ℂ)) (n : ℕ) (k : ℤ) (hk : k = n) (hn : Odd n)
    (x : Out.baseOver (Sp ℂ) ⟶ P.A) (hx : x ^ n = 1) :
    ∃ U : Out.ThetaGrp P.A P.L k (Out.overRes (T := Out.baseOver (Sp ℂ)) ⊤),
      Out.SymLift P.A P.L k n (Out.overResι ⊤ ≫ x) U := by
  subst hk
  have hu : IsUnit (n : Γ(Sp ℂ, ⊤)) := by
    have h : IsUnit (n : ℂ) := IsUnit.mk0 _ (by exact_mod_cast hn.pos.ne')
    simpa using h.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  obtain ⟨V, hV, U, hU⟩ := (hL.symLift (Sp ℂ) P n hn hu _ x hx).1 (default : PrimeSpectrum ℂ)
  obtain rfl : V = ⊤ := by
    refine top_le_iff.1 fun y _ => ?_
    have : y = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    rw [this]
    exact hV
  exact ⟨U, hU⟩

theorem ex_zero {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) :
    u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem

theorem ex_nsmul {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    (z : Fin g → ℂ) (n : ℕ) : u.ex (n • z) = u.ex z ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, ex_zero]
  | succ n ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]

theorem ex_sum {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    {r : ℕ} (z : Fin r → Fin g → ℂ) (a : Fin r → ℕ) :
    u.ex (∑ i, a i • z i) = Out.linComb (fun i => u.ex (z i)) a := by
  induction r with
  | zero => simp [Out.linComb, ex_zero]
  | succ r ih =>
    rw [Fin.sum_univ_succ, u.ex_add, ih, ex_nsmul]
    simp [Out.linComb, List.ofFn_succ]

theorem hasTh_classical : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (t : TObj g (N' ^ 2) J b (spMap em)) (u : HolUnif t.A t.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin g → ℂ) → ℂ) (lam : Fin (2 * g) → u.Λ), Odd N' → u.IsAH Hm χ → u.IsThetaFn Hm χ 1 θ → θ ≠ 0 → (∀ i, (t.pt i).left = (u.ex (((N' : ℂ) ^ 2)⁻¹ • (lam i : Fin g → ℂ))).left) → t.HasTh (𝟙 _) (fun a => χ (∑ i, ((a i).val : ℤ) • lam i) * Complex.exp (-(Real.pi / 2 / (N' : ℂ) ^ 2) * hermForm Hm (∑ i, ((a i).val : ℂ) • (lam i : Fin g → ℂ)) (∑ i, ((a i).val : ℂ) • (lam i : Fin g → ℂ))) * θ ((N' : ℂ)⁻¹ • ∑ i, ((a i).val : ℂ) • (lam i : Fin g → ℂ))) := by
  intro hL hL2 hT o _ g N' J b em t u Hm χ θ lam hN hAH hθ h0 hpt
  have hN0 : (N' : ℂ) ≠ 0 := by exact_mod_cast hN.pos.ne'
  haveI := t.ab.comm
  refine ⟨hN, ?_, fun q => ⟨⊤, trivial, ?_⟩⟩
  · have h : IsUnit (N' : ℂ) := IsUnit.mk0 _ hN0
    have h' := h.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    rw [map_natCast] at h'
    exact h'
  let T : Over (Sp ℂ) := Out.overRes (T := Out.baseOver (Sp ℂ)) ⊤
  haveI : IsIso T.hom := by
    show IsIso ((⊤ : (Sp ℂ).Opens).ι ≫ 𝟙 _)
    rw [Category.comp_id]
    exact inferInstanceAs (IsIso (Sp ℂ).topIso.hom)
  let p : 𝟙_ (Over (Sp ℂ)) ⟶ T := Over.homMk (inv T.hom) (by simp)
  have hp : p ≫ Out.overResι (T := Out.baseOver (Sp ℂ)) ⊤ = 𝟙 _ := by
    ext1
    show inv T.hom ≫ (⊤ : (Sp ℂ).Opens).ι = 𝟙 _
    rw [IsIso.inv_comp_eq]
    rfl
  have hpt' : t.pt = fun i => u.ex (((N' : ℂ) ^ 2)⁻¹ • (lam i : Fin g → ℂ)) :=
    funext fun i => Over.OverMorphism.ext (hpt i)
  have hcoe : ∀ a : Ix g (N' ^ 2), ((∑ i, ((a i).val : ℤ) • lam i : u.Λ) : Fin g → ℂ) =
      ∑ i, ((a i).val : ℂ) • (lam i : Fin g → ℂ) := fun a => by
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, natCast_zsmul, Nat.cast_smul_eq_nsmul]
  have hlab : ∀ a : Ix g (N' ^ 2), t.lab a =
      u.ex (((N' : ℂ) ^ 2)⁻¹ • ((∑ i, ((a i).val : ℤ) • lam i : u.Λ) : Fin g → ℂ)) := fun a => by
    rw [hcoe, Finset.smul_sum, TObj.lab, hpt']
    refine (ex_sum u _ _).symm.trans (congrArg u.ex (Finset.sum_congr rfl fun i _ => ?_))
    rw [smul_comm, Nat.cast_smul_eq_nsmul]
  have htor : ∀ a : Ix g (N' ^ 2), t.lab a ^ (N' ^ 2) = 1 := fun a => by
    rw [TObj.lab, Out.linComb, List.prod_ofFn, ← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← pow_mul, mul_comm, pow_mul, t.torsion, one_pow]
  have key := isThetaPtOver hL hL2 hT t.pol u Hm χ θ N' T p
    (fun a : Ix g (N' ^ 2) => Out.overResι ⊤ ≫ t.lab a) (fun a => ∑ i, ((a i).val : ℤ) • lam i)
    hN hAH hθ h0 (fun a => (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ t.lab a) hp).trans
      ((Category.id_comp _).trans (hlab a))))
    (fun a => exists_symLift hL t.pol (N' ^ 2) _ (by push_cast; rfl) hN.pow (t.lab a) (htor a))
  convert key using 2 with a a
  · congr 1
  · refine (constFn_top _).trans ?_
    refine congrArg (constFn T.hom ⊤) ?_
    exact congrArg (fun w : Fin g → ℂ => χ (∑ i, ((a i).val : ℤ) • lam i) *
      Complex.exp (-(Real.pi / 2 / (N' : ℂ) ^ 2) * hermForm Hm w w) * θ ((N' : ℂ)⁻¹ • w)) (hcoe a).symm

end GlobalTheory.ThetaClassical
end
