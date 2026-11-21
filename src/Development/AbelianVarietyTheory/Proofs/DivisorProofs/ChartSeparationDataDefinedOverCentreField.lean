import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionThetaValuesAbelianPartDefinedOver
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GsAppTopOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GmSpMapUnitOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkElementsApproxLeadingTermQuotients
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareApproxValuesAtPointOfElements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFourierTermSystemRegularTraitsGivenChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonModule
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosDefMapIntOfPos
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsConePullOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMonomialTauOfTauIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonomialTauOfPerFactor
import BuildAid.ForwardExisting

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.Coef

section Core

open GlobalTheory.UT GlobalTheory.UT.SymFrame ReciprocityTheory.ChartRestriction.G.DVR

variable {V₁ W₀ K : Type} [CommRing V₁] [IsDomain V₁] [CommRing W₀] [Field K] [IsAlgClosed K] {D : DegPre V₁}
  {B₀ : Over (Sp W₀)} [GrpObj B₀] {f : W₀ →+* V₁} {q : Fin 8 → (D.P.A.left ⟶ B₀.left)} {ev : V₁ →+* K} {k₀ : Subfield K}
  {X₂ : Scheme.{0}} {L₂ : LB X₂} {I : Type} [Fintype I] {π : I → (D.P.A.left ⟶ X₂)} {e : I → ℤ}
  {u : LB.Iso D.P.L (LB.LinComb L₂ π e)}

theorem step [IsLocalRing V₁] [IsNoetherianRing V₁] [IsIntegrallyClosed V₁] (H : Desc f q ev k₀ u) {N : ℕ} (hN : 1 ≤ N)
    (htor : ∀ x : Over.mk (spMap ev) ⟶ D.P.A, x ^ N = 1 → RatP q k₀ x.left)
    (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (g : GtPtF D (FractionRing V₁)) (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A)
    (hgb : g.b = toUnit _ ≫ b) (ho : ∃ o, GtPtF.IsNsmul N g o ∧ o.IsZero) (w : Frm D (FractionRing V₁) 1 g.b)
    (hw : w.IsGen ∧ ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1), Normd κ → ∀ z J, Good D.P.L z J →
      val w (𝟙 _) z J ^ (N ^ 2) * val κ g.b.left z J = 1) (χ : D.X)
    (hχ : RatP q k₀ (toUnit (Over.mk (spMap ev)) ≫ D.c χ).left)
    (t₃ : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (h₃ : t₃.IsGen)
    (m₃ : ∀ (z : Sp K) J J₂, Good D.P.L z J → Good L₂ z J₂ → ∃ c ∈ k₀,
      ((om (Z := Sp K) u z J J₂ (toUnit (Over.mk (spMap ev)) ≫ D.c χ).left)⁻¹ *
        val (Z := Sp K) t₃ (toUnit (Over.mk (spMap ev))).left z J).val = toStk z c) :
    ∃ R : V₁, (∀ z J, Good D.P.L z J → sval θ (cP D _ χ * g.b).left z J * (val (g.s χ) (𝟙 _) z J).val *
        (val w (𝟙 _) z J).val * (val t₃ (toUnit (TF (R := V₁) (FractionRing V₁))).left z J).val =
          cst (FractionRing V₁) z (algebraMap V₁ (FractionRing V₁) R)) ∧
      ∀ (z : Sp K) J J₂, Good D.P.L z J → Good L₂ z J₂ → ∃ c ∈ k₀, c ≠ 0 ∧ toStk z (ev R) = toStk z c *
        ((om (Z := Sp K) u z J J₂ (toUnit (Over.mk (spMap ev)) ≫ (D.c χ * b)).left).val *
          sval (Z := Sp K) θ (toUnit (Over.mk (spMap ev)) ≫ (D.c χ * b)).left z J) := by
  obtain ⟨t₁, h₁⟩ := exists_gen_of_local D.P.L D.P.isLB
    ![(D.c χ * b).left, (D.c χ).left, b.left, (η[D.P.A]).left] DegPre.gtε
  obtain ⟨t₂, h₂⟩ := exists_gen_of_local D.P.L D.P.isLB ![(η[D.P.A]).left, b.left] (DegPre.lineε 1)
  obtain ⟨a₁, g₁, m₁⟩ := char_mem H hN htor g b hgb ho χ hχ t₁ h₁
  obtain ⟨a₂, g₂, m₂⟩ := frame_mem H hN htor g b hgb ho w hw t₂ h₂
  obtain ⟨G, hG, vG⟩ := (((grep_gen (Y := 𝟙_ (Over (Sp V₁))) t₁ h₁ (𝟙 _)).mul (grep_gen t₂ h₂ (𝟙 _))).mul
    (grep_gen t₃ h₃ (𝟙 _))).inv.out D.P.isLB (fun k => (D.c χ * b).left ≫ D.famφB 0 k) (DegPre.famε 1) (fun U _ h => by
      rw [prod_gt (Z := Sp K), prod_ln, prod_famφB_zero, Fintype.prod_unique, Category.id_comp, zpow_neg_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  obtain ⟨x, hx⟩ := GlobalTheory.TwistUnit.exists_ratio_local D.P.isLB (H1.SectionArithmetic.pullSec θ (D.c χ * b).left) G hG
  have key : ∀ (T : Over (Sp V₁)) (z : T.left) J, Good D.P.L z J →
      sval θ (toUnit T ≫ (D.c χ * b)).left z J * (val t₁ (toUnit T).left z J * val t₂ (toUnit T).left z J *
        val t₃ (toUnit T).left z J).val = gs (toUnit T).left z ⊤ x := fun T z J hJ => by
    have e₁ := (H1.SectionArithmetic.sval_pullSec θ (D.c χ * b).left (toUnit T).left z hJ).symm.trans (hx _ (toUnit T).left z J hJ)
    have e₂ := vG T (toUnit T) z J hJ
    simp only [Category.comp_id] at e₂
    refine (congrArg (· * _) (e₁.trans (congrArg (fun t => _ * Units.val t) e₂))).trans ?_
    rw [_root_.mul_assoc]
    erw [Units.inv_mul, _root_.mul_one]
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of V₁)).hom.hom x * a₁ * a₂, fun z J hJ => ?_, fun z J J₂ hJ hJ₂ => ?_⟩
  · have e₁ := (key _ z J hJ).trans (gs_gen x z)
    have e₂ : cP D _ χ * g.b = toUnit (TF (R := V₁) (FractionRing V₁)) ≫ (D.c χ * b) := by
      rw [hgb, MonObj.comp_mul]; rfl
    rw [e₂, g₁ z J hJ, g₂ z J hJ]
    simp only [CoefBasic.cst_eq, map_mul, Units.val_mul] at e₁ ⊢
    rw [← e₁]
    ring
  · have e₁ := (key (Over.mk (spMap ev)) z J hJ).trans (gs_ev ev x z)
    obtain ⟨c₁, hc₁, n₁⟩ := m₁ z J J₂ hJ hJ₂
    obtain ⟨c₂, hc₂, n₂⟩ := m₂ z J J₂ hJ hJ₂
    obtain ⟨c₃, hc₃, n₃⟩ := m₃ z J J₂ hJ hJ₂
    have ne : ∀ {c : K} {s : (Sp K).presheaf.stalk z}, IsUnit s → s = toStk z c → c ≠ 0 := by
      rintro c s hs e rfl
      rw [e, map_zero] at hs
      exact not_isUnit_zero hs
    refine ⟨c₁ * c₂ * c₃, k₀.mul_mem (k₀.mul_mem hc₁ hc₂) hc₃, mul_ne_zero (mul_ne_zero
      (ne (((a₁.isUnit.map ev).map _).mul (Units.isUnit _)) n₁) (ne (((a₂.isUnit.map ev).map _).mul (Units.isUnit _)) n₂))
      (ne (Units.isUnit _) n₃), ?_⟩
    have alg : ∀ {S : Type} [CommRing S] (p c b o v₁ v₂ v₃ : Sˣ) (s a₁ a₂ : S),
        s * (v₁ * v₂ * v₃).val * a₁ * a₂ = a₁ * (p⁻¹ * c * b * o⁻¹ * v₁).val * (a₂ * (o * b⁻¹ * v₂).val) *
          (c⁻¹ * v₃).val * (p.val * s) := by
      intro S _ p c b o v₁ v₂ v₃ s a₁ a₂
      have : v₁ * v₂ * v₃ = (p⁻¹ * c * b * o⁻¹ * v₁) * (o * b⁻¹ * v₂) * (c⁻¹ * v₃) * p := by
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
      rw [this]
      generalize p⁻¹ * c * b * o⁻¹ * v₁ = A
      generalize o * b⁻¹ * v₂ = B
      generalize c⁻¹ * v₃ = C
      simp only [Units.val_mul]
      ring
    simp only [map_mul]
    rw [← n₁, ← n₂, ← n₃, ← e₁]
    exact alg _ _ _ _ _ _ _ _ _ _

theorem core [IsLocalRing V₁] (hV : IsCN V₁) (H : Desc f q ev k₀ u) {N : ℕ} (hN : 2 ≤ N) (hNK : (N : K) ≠ 0)
    (htor : ∀ x : Over.mk (spMap ev) ⟶ D.P.A, x ^ N = 1 → RatP q k₀ x.left)
    {X C : Type} [AddCommGroup X] (eX : X ≃+ D.X) (T : X → C → V₁) (hT : IsThetaTerms D N eX T)
    (hc : ∀ mu, RatP q k₀ (toUnit (Over.mk (spMap ev)) ≫ D.c (eX mu)).left) (y : X → FractionRing V₁) (hy : y 0 = 1)
    (hψ : ∀ mu, ∃ t : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c (eX mu)).left) (fun _ => -1)), t.IsGen ∧
      (∀ (z : (TF (R := V₁) (FractionRing V₁)).left) J, Good D.P.L z J →
        (val (D.psi (eX mu)) (jFK (R := V₁) (FractionRing V₁)) z J).val =
          (val t (toUnit (TF (R := V₁) (FractionRing V₁))).left z J).val * cst (FractionRing V₁) z (y mu)) ∧
      ∀ (z : Sp K) J J₂, Good D.P.L z J → Good L₂ z J₂ → ∃ c ∈ k₀,
        ((om (Z := Sp K) u z J J₂ (toUnit (Over.mk (spMap ev)) ≫ D.c (eX mu)).left)⁻¹ *
          val (Z := Sp K) t (toUnit (Over.mk (spMap ev))).left z J).val = toStk z c) (mu : X) (c : C) :
    ∃ R R₀ : V₁, algebraMap V₁ (FractionRing V₁) (T mu c * R₀) = algebraMap V₁ (FractionRing V₁) R * y mu ∧
      ev R₀ ≠ 0 ∧ ∃ r ∈ k₀, ev R = r * ev R₀ := by
  haveI : IsNoetherianRing V₁ := hV.1
  haveI : IsIntegrallyClosed V₁ := hV.2.1
  obtain ⟨th, g, b, w, h₁, h₂, h₃, h₄, h₅, c₀, h₆⟩ := hT
  obtain ⟨θ, hθ, hnz, hlam, -, -⟩ := ThetaOne.main hV D
  obtain ⟨lam, hlam, -⟩ := hlam (FractionRing V₁) th
  choose t ht gt mt using hψ
  choose R gR mR using fun mu c => step H (by omega) htor θ (g c) (b c) (h₁ c) (h₂ c) (w c) (h₄ c) (eX mu) (hc mu) (t mu)
    (ht mu) (mt mu)
  obtain ⟨κ, hκ, hθκ⟩ := theta_mem H θ (hθ K ev)
  obtain ⟨z⟩ := CoefBasic.exists_pt (R := V₁) (F := FractionRing V₁)
  obtain ⟨J, hJ⟩ := CoefBasic.exists_good' D.P.isLB z
  have gen : ∀ mu c, CoefBasic.cstH z (algebraMap V₁ (FractionRing V₁) (T mu c)) *
      (rigV D (TF (R := V₁) (FractionRing V₁)).hom z J).val =
      cst (FractionRing V₁) z lam * (@id ((TF (R := V₁) (FractionRing V₁)).left.presheaf.stalk z)ˣ
        (val (D.psi 0) (jFK (R := V₁) (FractionRing V₁)) z J))⁻¹.val *
        CoefBasic.cstH z (algebraMap V₁ (FractionRing V₁) (R mu c) * y mu) := fun mu c => by
    have e₁ := h₅ mu c z J hJ
    rw [pow_one, term_val D _ th θ lam hlam _ _ z J hJ, Units.val_mul] at e₁
    have e₂ : (@id ((TF (R := V₁) (FractionRing V₁)).left.presheaf.stalk z)ˣ
      (val (D.psi (eX mu)) (jFK (R := V₁) (FractionRing V₁)) z J)).val = _ := gt mu z J hJ
    rw [map_mul, ← CoefBasic.cst_eq, ← CoefBasic.cst_eq, ← CoefBasic.cst_eq, e₁, e₂, ← gR mu c z J hJ]
    ring
  have rel : ∀ mu c, algebraMap V₁ (FractionRing V₁) (T mu c * R 0 c₀) =
      algebraMap V₁ (FractionRing V₁) (R mu c) * y mu := fun mu c => by
    have e₀ := gen 0 c₀
    rw [h₆, hy, map_one, map_one, _root_.one_mul, _root_.mul_one] at e₀
    have e₁ := gen mu c
    refine CoefBasic.cstH_inj z ((rigV D (TF (R := V₁) (FractionRing V₁)).hom z J).isUnit.mul_right_cancel ?_)
    rw [map_mul, map_mul]
    linear_combination CoefBasic.cstH z (algebraMap V₁ (FractionRing V₁) (R 0 c₀)) * e₁ -
      CoefBasic.cstH z (algebraMap V₁ (FractionRing V₁) (R mu c) * y mu) * e₀
  let zK : Sp K := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  obtain ⟨JK, hJK⟩ := CoefBasic.exists_good' D.P.isLB zK
  obtain ⟨J₂, hJ₂⟩ := CoefBasic.exists_good' H.hL₂ zK
  have inK : ∀ mu c, ∃ r ∈ k₀, ev (R mu c) = κ * r := fun mu c => by
    obtain ⟨r, hr, -, e₁⟩ := mR mu c zK JK J₂ hJK hJ₂
    obtain ⟨r', hr', e₂⟩ := hθκ (toUnit _ ≫ (D.c (eX mu) * b c)) (by
      rw [MonObj.comp_mul]
      refine ratP_mul H.hP H.hk (hc mu) (htor _ ?_)
      rw [← MonObj.comp_pow, (Frames.torsion_of_nsmul (g c) (b c) (h₁ c) (h₂ c)).2, MonObj.comp_one]) zK JK J₂ hJK hJ₂
    rw [e₂, ← map_mul] at e₁
    exact ⟨r * r', k₀.mul_mem hr hr', ((toStk zK).injective e₁).trans (mul_left_comm _ _ _)⟩
  have ne : ev (R 0 c₀) ≠ 0 := fun h0 => by
    obtain ⟨p, hp, hne⟩ := exists_torsion_ne D ev θ (hnz K ev) N hN hNK
    obtain ⟨c₁, rfl⟩ := h₃ K (spMap ev) p hp
    obtain ⟨r, -, hr, e₁⟩ := mR 0 c₁ zK JK J₂ hJK hJ₂
    have e₂ := rel 0 c₁
    rw [hy, _root_.mul_one] at e₂
    rw [← IsFractionRing.injective V₁ (FractionRing V₁) e₂, map_mul, h0, mul_zero, map_zero, map_zero eX, ThetaOne.c_zero,
      _root_.one_mul] at e₁
    have u₁ : IsUnit (toStk zK r) := (IsUnit.mk0 r hr).map _
    exact hne zK JK hJK ((Units.mul_right_eq_zero _).1 (u₁.mul_right_eq_zero.1 e₁.symm))
  obtain ⟨r, hr, e₁⟩ := inK mu c
  obtain ⟨r₀, hr₀, e₀⟩ := inK 0 c₀
  have h0 : r₀ ≠ 0 := by
    rintro rfl
    exact ne (e₀.trans (mul_zero _))
  refine ⟨R mu c, R 0 c₀, rel mu c, ne, r / r₀, k₀.div_mem hr hr₀, ?_⟩
  rw [e₁, e₀]
  field_simp

end Core

section Main

open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem prod_split {V₁ : Type} [CommRing V₁] [IsDomain V₁] {m N : ℕ} (s : Fin m ⊕ Fin N → V₁) (n : Fin m ⊕ Fin N → ℤ)
    (σ : Fin N → V₁ˣ) (hσ : ∀ k, (σ k : V₁) = s (.inr k)) (hn : ∀ k, 0 ≤ n (.inl k)) :
    ∏ i : Fin (m + N), algebraMap V₁ (FractionRing V₁) (s (finSumFinEquiv.symm i)) ^ n (finSumFinEquiv.symm i) =
      algebraMap V₁ (FractionRing V₁) ((∏ k, s (.inl k) ^ (n (.inl k)).toNat) * (∏ k, σ k ^ n (.inr k)).val) := by
  rw [Equiv.prod_comp finSumFinEquiv.symm (fun i => algebraMap V₁ (FractionRing V₁) (s i) ^ n i), Fintype.prod_sum_type,
    map_mul, map_prod, Units.coe_prod, map_prod]
  congr 1
  · exact Finset.prod_congr rfl fun k _ => by rw [map_pow, ← zpow_natCast, Int.toNat_of_nonneg (hn k)]
  · refine Finset.prod_congr rfl fun k _ => ?_
    rw [← hσ]
    exact ((congrArg Units.val (map_zpow (Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom) (σ k) _)).trans
      (Units.val_zpow_eq_zpow_val _ _)).symm

theorem coef_monomial : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (τ₀ : Gens Q) (m N : ℕ) (s : Fin m ⊕ Fin N → V) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ Q.X), (∀ k, IsUnit (s (.inr k))) → (∀ k mu, 0 ≤ qW W (ε (.inl k)) mu) → TauIn Q τ₀ (fun k => s (finSumFinEquiv.symm k)) (fun k => ε (finSumFinEquiv.symm k)) → (∀ mu, mo mu = mono W (fun k => ρ (s (.inl k))) (fun k => ε (.inl k)) mu) → ∀ (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V), FromBase Q τ₀ ib → (∀ a, ev (ρ (ib a)) ∈ k₀) → ∀ mu c, ∃ r ∈ k₀, ev (u mu c) = r * ∏ k, ev (ρ (s (.inr k))) ^ qW W (ε (.inr k)) mu := by
  intro g l hl _ W _
  refine ⟨1, ?_⟩
  intro j hj V V₁ _ _ _ _ _ hV hlu Q _ ρ hρ D e hS C u mo hmo hT K _ _ ev k₀ hk₀ τ₀ m N s ε hs hε hτ hmono W₀ _ ib hB hk mu c
  haveI : IsNoetherianRing V₁ := hV.1
  obtain ⟨pr, w, hpr, huniv, hw, hc, B₀, iG, iC, M₀, c₀, τ₁, β, β₂, w₀, -, hM₀, hβ, hsq, hw₀, hβc, hτ₁, -, hψ⟩ :=
    PsiMono.psi_val_of W Q ρ hρ D e hS τ₀ _ _ hτ ib hB
  obtain ⟨Ω, hΩ, vΩ⟩ := exists_omega W ρ Q D pr B₀ β₂ w hw M₀ hM₀ w₀ hw₀
  have hN : 2 ≤ (l ^ j) ^ 2 := hl.two_le.trans ((Nat.le_self_pow (by omega) l).trans (Nat.le_self_pow (by omega) _))
  have hNu : IsUnit (((l ^ j) ^ 2 : ℕ) : V₁) := by push_cast; exact (hlu.pow _).pow _
  have htor : ∀ x : Over.mk (spMap ev) ⟶ D.P.A, x ^ ((l ^ j) ^ 2) = 1 →
      RatP (fun a => (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β) k₀ x.left := fun x hx a =>
    sharp_torsion_defOver ρ ib Q D pr hpr huniv B₀ β hβ K ev k₀ hk₀ hk _ (by omega) hNu x hx a
  have h2 : spMap (ρ.comp ib) = spMap ρ ≫ spMap ib := by
    simp only [spMap, ← Spec.map_comp]; rfl
  have H : Desc (ρ.comp ib) (fun a => (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β) ev k₀ Ω :=
    ⟨hk₀, fun T g hg => exists_points_equiv ρ ib Q D pr hpr huniv B₀ β hβ T.hom g (h2 ▸ hg), hk, hM₀, hΩ,
      piB_congr ρ Q D pr B₀ β₂ hsq, htor 1 (one_pow _)⟩
  obtain ⟨R, R₀, e₁, hne, r, hr, e₂⟩ := core hV H hN (by simpa using (hNu.map ev).ne_zero) htor e _ hT
    (fun mu a => sharp_c_defOver ρ ib Q D e pr hc B₀ β c₀ hβc K ev k₀ hk mu a)
    (fun mu => ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (s (finSumFinEquiv.symm i))) ^ qW W (ε (finSumFinEquiv.symm i)) mu)
    (by simp [qW]) (fun mu => by
      obtain ⟨t, ht, vt⟩ := exists_psi_gen W ρ Q D pr B₀ β₂ hM₀ hsq Ω hΩ (spMap ρ ≫ spMap ib) (D.c (e mu))
        (fun a => c₀ (mu a)) (fun a => by
          have := congrArg (· ≫ β) (hc mu a)
          simp only [Category.assoc, Over.comp_left, hβc] at this ⊢
          exact this) (fun a b => τ₁ (mu a) (mu b)) (fun a b => hτ₁ _ _)
      refine ⟨t, ht, fun z J hJ => ?_, fun z J J₂ hJ hJ₂ => ?_⟩
      · obtain ⟨JQ, hJQ⟩ := CoefBasic.exists_good' Q.M.isLB z
        obtain ⟨J₀, hJ₀⟩ := CoefBasic.exists_good' hM₀ z
        obtain ⟨y, hy, ey⟩ := hψ mu z JQ J J₀ hJQ hJ hJ₀
        have j1 : jFK (R := V₁) (FractionRing V₁) = 𝟙 _ := Spec.map_id _
        have t1 : (toUnit (TF (R := V₁) (FractionRing V₁))).left = (toUnit (TK V₁)).left := by
          show jFK (R := V₁) (FractionRing V₁) ≫ jK V₁ = jK V₁
          rw [j1]; exact Category.id_comp _
        have et := vt (TK V₁) z J J₀ hJ hJ₀
        rw [vΩ _ _ z J JQ J₀ hJ hJQ hJ₀] at et
        have pe : ∀ a b, (toUnit (TK V₁) ≫ D.c (e mu)).left ≫ sharpPair ρ Q D pr a b =
            (lift (toUnit (PsiMono.fracOver ρ hρ) ≫ Q.c (mu a)) (toUnit (PsiMono.fracOver ρ hρ) ≫ Q.c (mu b))).left := by
          have k : ∀ a, (toUnit (TK V₁) ≫ D.c (e mu)).left ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) =
              (toUnit (PsiMono.fracOver ρ hρ) ≫ Q.c (mu a)).left := fun a => by
            show (jK V₁ ≫ (D.c (e mu)).left) ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) =
              (PsiMono.fracPt ρ hρ ≫ jK V) ≫ (Q.c (mu a)).left
            rw [PsiMono.fracPt_comp]
            exact (Category.assoc _ _ _).trans ((congrArg (jK V₁ ≫ ·) (hc mu a)).trans (Category.assoc _ _ _).symm)
          intro a b
          have hP := isGrpPullback_pullback Q.B (spMap ρ)
          apply pullback.hom_ext
          · refine Eq.trans ?_ ((k a).trans (congrArg (fun m => m.left) (lift_fst
              (toUnit (PsiMono.fracOver ρ hρ) ≫ Q.c (mu a)) (toUnit (PsiMono.fracOver ρ hρ) ≫ Q.c (mu b)))).symm)
            exact (Category.assoc _ _ _).trans (congrArg (fun m => (toUnit (TK V₁) ≫ D.c (e mu)).left ≫ m.left)
              (lift_fst (pushPt hP.1.w (pr a)) (pushPt hP.1.w (pr b))))
          · refine Eq.trans ?_ ((k b).trans (congrArg (fun m => m.left) (lift_snd
              (toUnit (PsiMono.fracOver ρ hρ) ≫ Q.c (mu a)) (toUnit (PsiMono.fracOver ρ hρ) ≫ Q.c (mu b)))).symm)
            exact (Category.assoc _ _ _).trans (congrArg (fun m => (toUnit (TK V₁) ≫ D.c (e mu)).left ≫ m.left)
              (lift_snd (pushPt hP.1.w (pr a)) (pushPt hP.1.w (pr b))))
        have ge : (TK V₁).hom ≫ spMap ρ ≫ spMap ib = (PsiMono.fracPt ρ hρ ≫ jK V) ≫ spMap ib := by
          rw [PsiMono.fracPt_comp]; exact (Category.assoc _ _ _).symm
        simp only [pe, ge] at et
        simp only [mul_zpow, Finset.prod_mul_distrib] at ey
        rw [j1, t1, ← hy]
        refine (congrArg Units.val (ey.trans (congrArg (· * _) ((_root_.mul_assoc _ _ _).symm.trans et.symm)))).trans ?_
        exact (Units.val_mul _ _).trans (congrArg₂ (· * ·) rfl (gs_unit _ _ ⊤ trivial _).symm)
      · have et := vt (Over.mk (spMap ev)) z J J₂ hJ hJ₂
        obtain ⟨x, hx, ex⟩ := prod_mem (k₀ := k₀) (z := z) Finset.univ (fun a => prod_mem Finset.univ fun b =>
          zpow_mem (val_spMap_mem k₀ (τ₁ (mu a) (mu b)) ((ev.comp ρ).comp ib) hk z hJ₂) (W a b))
        refine ⟨x, hx, Eq.trans (congrArg Units.val ?_) ex⟩
        rw [← spMap_three]
        exact inv_mul_eq_iff_eq_mul.2 et) mu c
  refine ⟨r, hr, ?_⟩
  have e₃ := prod_split (fun i => ρ (s i)) (fun i => qW W (ε i) mu) (fun k => ((hs k).map ρ).unit) (fun _ => rfl)
    (fun k => hε k mu)
  rw [e₃, ← map_mul] at e₁
  have e₄ := IsFractionRing.injective V₁ (FractionRing V₁) e₁
  have e₅ : ∏ k, ρ (s (.inl k)) ^ (qW W (ε (.inl k)) mu).toNat = mo mu := (hmono mu).symm
  rw [e₅] at e₄
  have e₆ : u mu c * R₀ = R * (∏ k, ((hs k).map ρ).unit ^ qW W (ε (.inr k)) mu).val :=
    mul_left_cancel₀ (hmo mu).1 (by linear_combination e₄)
  have e₇ : ev (∏ k, ((hs k).map ρ).unit ^ qW W (ε (.inr k)) mu).val =
      ∏ k, ev (ρ (s (.inr k))) ^ qW W (ε (.inr k)) mu := by
    rw [Units.coe_prod, map_prod]
    exact Finset.prod_congr rfl fun k _ => (congrArg Units.val (map_zpow (Units.map ev.toMonoidHom) _ _)).trans
      (Units.val_zpow_eq_zpow_val _ _)
  have e₈ := congrArg ev e₆
  rw [map_mul, map_mul, e₇, e₂] at e₈
  exact mul_right_cancel₀ hne (by linear_combination e₈)

end Main

end GlobalTheory.Poinc.Sep.Coef
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighthPower_thetaCoefficient_eq_const_mul_monomial : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (τ₀ : Gens Q) (m N : ℕ) (s : Fin m ⊕ Fin N → V) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ Q.X), (∀ k, IsUnit (s (.inr k))) → (∀ k mu, 0 ≤ qW W (ε (.inl k)) mu) → TauIn Q τ₀ (fun k => s (finSumFinEquiv.symm k)) (fun k => ε (finSumFinEquiv.symm k)) → (∀ mu, mo mu = mono W (fun k => ρ (s (.inl k))) (fun k => ε (.inl k)) mu) → ∀ (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V), FromBase Q τ₀ ib → (∀ a, ev (ρ (ib a)) ∈ k₀) → ∀ mu c, ∃ r ∈ k₀, ev (u mu c) = r * ∏ k, ev (ρ (s (.inr k))) ^ qW W (ε (.inr k)) mu := by
  atlas_forward_decl GlobalTheory.Poinc.Sep.Coef.coef_monomial
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stalk_elements_approx_leadingTerm_quotients : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∀ (φ : InvFun ℤ) (d : ℕ) (J : Z.IdealSheafData) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S), (∀ x ∈ J.support, x ∉ Set.range i) → ValOn F i φ J d → IsNormBl π J → j ≫ π = i → IsPolFan id g φ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), Module.finrank ℤ Q.X ≤ g → (∀ k, t k ∈ maximalIdeal V ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → Q.IsMonomialTau t δ → ∀ (ga : Fin m → LinearMap.BilinForm ℤ Q.X) (M : ℕ), 1 ≤ M → IsCone id φ ga → (∀ k, δ k = (M : ℤ) • ga k) → ∀ ξ : Sp V ⟶ S, UnifOver F j ξ Q → ∀ (N₁ : ℕ) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (Φ : VSys (id : ℤ → ℤ) g W N₁ (X₁.M.Z.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃+ Q.X) (h : Fin (Φ.m y) ≃ Fin m), HasTraitsR X₁ z₁ Φ.pre → IsChartMember X₁ z₁ Φ Q (ξ ≫ π) t δ y ρ e h → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ p, (spMap ev ≫ ξ) p = ξ (closedPoint V)) → DefOver k₀ (spMap ev ≫ ξ) → ∀ ga' : Fin (Φ.m y) → LinearMap.BilinForm ℤ (Φ.X y), (∀ k a b, ga' k a b = ga (h k) (e a) (e b)) → ∃ ev₁ : Φ.V y →+* K, ev₁.comp ρ = ev ∧ Elements Φ y φ d ga' ev₁ k₀ := by
  first | exact @GlobalTheory.CoverElements.exists_elements | exact GlobalTheory.CoverElements.exists_elements | (intros; apply GlobalTheory.CoverElements.exists_elements <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem isMonomialTau_inl_of_tauIn : ∀ (V : Type) [CommRing V] [IsDomain V] (Q : Data V) (τ₀ : GlobalTheory.Poinc.Sep.Gens Q) (m N : ℕ) (s : Fin m ⊕ Fin N → V) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ Q.X), (∀ k, IsUnit (s (.inr k))) → GlobalTheory.Poinc.Sep.TauIn Q τ₀ (fun k => s (finSumFinEquiv.symm k)) (fun k => ε (finSumFinEquiv.symm k)) → Q.IsMonomialTau (fun k => s (.inl k)) (fun k => ε (.inl k)) := by
  intro V _ _ Q τ₀ m N s ε hs h a b
  obtain ⟨k, hk, hc⟩ := Model.isMonomialTau_of_tauIn h a b
  let alg : V →* FractionRing V := (algebraMap V (FractionRing V) : V →* FractionRing V)
  let w : Vˣ := ∏ j : Fin N, (hs j).unit ^ ε (.inr j) a b
  refine ⟨k * Units.map alg w⁻¹, ?_, GlobalTheory.PolDeg.Taut.tauCoord_mul_unit hc w⁻¹⟩
  have hprod : (k : FractionRing V) = (∏ i : Fin m, algebraMap V (FractionRing V) (s (.inl i)) ^ ε (.inl i) a b) *
      ∏ j : Fin N, algebraMap V (FractionRing V) (s (.inr j)) ^ ε (.inr j) a b := by
    rw [hk, ← Fintype.prod_sum_type (fun x => algebraMap V (FractionRing V) (s x) ^ ε x a b)]
    exact Fintype.prod_equiv finSumFinEquiv.symm _ _ (fun _ => rfl)
  have hw : ((Units.map alg w : (FractionRing V)ˣ) : FractionRing V) =
      ∏ j : Fin N, algebraMap V (FractionRing V) (s (.inr j)) ^ ε (.inr j) a b := by
    simp [w, alg, Units.coe_prod, map_zpow₀]
  rw [Units.val_mul, map_inv, Units.val_inv_eq_inv_val, hw, hprod, mul_inv_cancel_right₀]
  exact Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _
    ((IsFractionRing.injective V (FractionRing V)).ne_iff' (map_zero _) |>.2 (hs j).ne_zero)

end GlobalTheory.Poinc.Sep
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMonomialTau_first_coords_of_unit_last_coords : ∀ (V : Type) [CommRing V] [IsDomain V] (Q : Data V) (τ₀ : GlobalTheory.Poinc.Sep.Gens Q) (m N : ℕ) (s : Fin m ⊕ Fin N → V) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ Q.X), (∀ k, IsUnit (s (.inr k))) → GlobalTheory.Poinc.Sep.TauIn Q τ₀ (fun k => s (finSumFinEquiv.symm k)) (fun k => ε (finSumFinEquiv.symm k)) → Q.IsMonomialTau (fun k => s (.inl k)) (fun k => ε (.inl k)) := by
  atlas_forward_decl GlobalTheory.Poinc.Sep.isMonomialTau_inl_of_tauIn
end

section
section
namespace GlobalTheory

theorem exists_pos_mul_extend_int_linearForm (F : Type) [AddCommGroup F] [Module.Free ℤ F]
    [Module.Finite ℤ F] (P : Submodule ℤ F) (f : P →ₗ[ℤ] ℤ) :
    ∃ c : ℤ, 0 < c ∧ ∃ lam : F →ₗ[ℤ] ℤ, ∀ x : P, lam x = c * f x := by
  classical
  obtain ⟨g, hg⟩ := (Module.Baer.of_divisible ℚ).extension_property P.subtype
    P.injective_subtype ((Algebra.linearMap ℤ ℚ).comp f)
  let b := Module.Free.chooseBasis ℤ F
  obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (S := ℚ) (fun i => g (b i))
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  choose n hn using hint
  let lam : F →ₗ[ℤ] ℤ := b.constr ℤ n
  have key : (Algebra.linearMap ℤ ℚ).comp lam = d • g := by
    refine b.ext fun i => ?_
    simpa [lam] using hn i
  refine ⟨d * d, mul_self_pos.mpr hd0, d • lam, fun x => ?_⟩
  have h1 := LinearMap.congr_fun key x
  have h2 := LinearMap.congr_fun hg x
  simp at h1 h2
  rw [h2] at h1
  have h3 : lam x = d * f x := by exact_mod_cast h1
  simp [h3, mul_assoc]

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pos_mul_extend_int_linearForm' : ∀ (F : Type) [AddCommGroup F] [Module.Free ℤ F] [Module.Finite ℤ F] (P : Submodule ℤ F) (f : P →ₗ[ℤ] ℤ), ∃ c : ℤ, 0 < c ∧ ∃ lam : F →ₗ[ℤ] ℤ, ∀ x : P, lam x = c * f x := by
  atlas_forward_decl GlobalTheory.exists_pos_mul_extend_int_linearForm
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.Poinc.Sep.Assembly

theorem monoTau_inl {V : Type} [CommRing V] [IsDomain V] (Q : Data V) (τ₀ : Gens Q) {m N : ℕ} (s : Fin m ⊕ Fin N → V)
    (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ Q.X) (hs : ∀ k, IsUnit (s (.inr k)))
    (h : TauIn Q τ₀ (fun k => s (finSumFinEquiv.symm k)) (fun k => ε (finSumFinEquiv.symm k))) :
    Q.IsMonomialTau (fun k => s (.inl k)) (fun k => ε (.inl k)) :=
  GlobalTheory.T.isMonomialTau_first_coords_of_unit_last_coords V Q τ₀ m N s ε hs h

theorem unifOver_comp {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S Z : Scheme.{0}} (j : F.X ⟶ S)
    (π : S ⟶ Z) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (ξ : Sp V ⟶ S) (Q : Data V)
    (h : UnifOver F j ξ Q) : UnifOver F (j ≫ π) (ξ ≫ π) Q := by
  refine ⟨h.1, fun R' _ _ _ ρ hc hi hf D ε hR => ?_⟩
  obtain ⟨G', i1, i2, A, i3, y', α, α₂, h1, h2, h3, h4, h5⟩ := h.2 R' ρ hc hi hf D ε hR
  exact ⟨G', i1, i2, A, i3, y', α, α₂, h1, by rw [← Category.assoc, h2]; simp only [Category.assoc], h3, h4, h5⟩

theorem isUnit_natCast_of_cyc (n : ℕ) (hn : n ≠ 0) (V : Type) [CommRing V] (f : Sp V ⟶ Sp (cycAway n)) :
    IsUnit ((n : ℕ) : V) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  simpa using (isUnit_natCast hn).map φ.hom

theorem exists_ext_functional (F : Type) [AddCommGroup F] [Module.Free ℤ F] [Module.Finite ℤ F] (P : Submodule ℤ F)
    (f : P →ₗ[ℤ] ℤ) : ∃ c : ℤ, 0 < c ∧ ∃ lam : F →ₗ[ℤ] ℤ, ∀ x : P, lam x = c * f x :=
  GlobalTheory.T.exists_pos_mul_extend_int_linearForm' F P f

theorem isCone_inst {φ : InvFun ℤ} {X : Type} [AddCommGroup X] (i1 i2 : Module ℤ X) [f1 : @Module.Finite ℤ X _ _ i1]
    [f2 : @Module.Finite ℤ X _ _ i2] {m : ℕ} (gm' : Fin m → @LinearMap.BilinForm ℤ _ X _ (AddCommGroup.toIntModule X))
    (h : @IsCone ℤ _ id φ X _ i1 f1 m gm') : @IsCone ℤ _ id φ X _ i2 f2 m gm' := by
  obtain rfl : i1 = i2 := Subsingleton.elim _ _
  exact h

theorem isCone_equiv {φ : InvFun ℤ} {X X₁ : Type} [AddCommGroup X] [Module.Finite ℤ X] [AddCommGroup X₁]
    [Module.Finite ℤ X₁] (hF : IsPolFanOn id φ X) {m m' : ℕ} (gm' : Fin m → LinearMap.BilinForm ℤ X₁)
    (hgm' : IsCone id φ gm') (e : X ≃ₗ[ℤ] X₁) (h : Fin m' ≃ Fin m) :
    IsCone id φ (fun k => LinearMap.BilinForm.congr e.symm (gm' (h k))) := by
  have h1 := isCone_pull_of_surjective ℤ id X φ X₁ e.toLinearMap m gm' hF e.surjective hgm'
  have h2 := hF.face m m' _ h.toEmbedding h1
  convert h2 using 2 with k
  ext a b
  simp [pull]

theorem prod_zpow_eq {K ιt : Type} [Field K] {x : K} (hx : x ≠ 0) (s : Finset ιt) (f : ιt → ℤ) :
    ∏ i ∈ s, x ^ f i = x ^ ∑ i ∈ s, f i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add₀ hx]

theorem mem_of_pow_mem {K : Type} [Field K] (k₀ : Subfield K) (hk : IsAlgClosed k₀) (x : K) (p : ℕ) (hp : 0 < p)
    (h : x ^ p ∈ k₀) : x ∈ k₀ := by
  haveI := hk
  have hint : IsIntegral k₀ x := by
    refine ⟨Polynomial.X ^ p - Polynomial.C ⟨x ^ p, h⟩, Polynomial.monic_X_pow_sub_C _ (by omega), ?_⟩
    simp [Polynomial.eval₂_sub]
    exact sub_eq_zero.2 rfl
  have h1 := IsAlgClosed.degree_eq_one_of_irreducible k₀ (minpoly.irreducible hint)
  obtain ⟨c, hc⟩ := minpoly.natDegree_eq_one_iff.1 (Polynomial.natDegree_eq_of_degree_eq_some h1)
  rw [← hc]
  exact c.2

theorem mem_of_ratio {K : Type} [Field K] (k₀ : Subfield K) (hk : IsAlgClosed k₀) {X R C : Type} [AddCommGroup X]
    [CommRing R] (ev₁ : R →+* K) (u : (Fin 8 → X) → C → R) (W : Matrix (Fin 8) (Fin 8) ℤ) {N : ℕ} (x : Fin N → K)
    (hx : ∀ k, x k ≠ 0) (gm' : Fin N → LinearMap.BilinForm ℤ X)
    (hu : ∀ mu c, ∃ r ∈ k₀, ev₁ (u mu c) = r * ∏ k, x k ^ qW W (gm' k) mu) {l l' : ℕ} (a : Fin l × Fin 8 → X)
    (a' : Fin l' × Fin 8 → X) (c : Fin l → C) (c' : Fin l' → C) (ha : IsUnit (∏ i, u (fun v => a (i, v)) (c i)))
    (k : Fin N) (p : ℤ) (hp : 0 < p) (hlin : ∀ k', lin W a (gm' k') - lin W a' (gm' k') = if k' = k then p else 0)
    (hr : ∃ r ∈ k₀, ev₁ (∏ i, u (fun v => a (i, v)) (c i)) = r * ev₁ (∏ i, u (fun v => a' (i, v)) (c' i))) :
    x k ∈ k₀ := by
  have key : ∀ {l : ℕ} (a : Fin l × Fin 8 → X) (c : Fin l → C), ∃ Rr ∈ k₀,
      ev₁ (∏ i, u (fun v => a (i, v)) (c i)) = Rr * ∏ k, x k ^ lin W a (gm' k) := by
    intro l a c
    choose rr hrr heq using hu
    refine ⟨∏ i, rr (fun v => a (i, v)) (c i), prod_mem fun i _ => hrr _ _, ?_⟩
    rw [map_prod]
    simp_rw [heq]
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [prod_zpow_eq (hx k)]
    rfl
  obtain ⟨Rr, hR, hReq⟩ := key a c
  obtain ⟨Rr', hR', hR'eq⟩ := key a' c'
  obtain ⟨r, hr, hrr⟩ := hr
  have hne : ev₁ (∏ i, u (fun v => a (i, v)) (c i)) ≠ 0 := (ha.map ev₁).ne_zero
  have hP : ∀ (b : Fin N → ℤ), ∏ k, x k ^ b k ≠ 0 := fun b =>
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hx k)
  have hR0 : Rr ≠ 0 := by intro h0; rw [h0, zero_mul] at hReq; exact hne hReq
  have hxp : x k ^ p = r * Rr' / Rr := by
    have e1 : x k ^ p = ∏ k', x k' ^ (lin W a (gm' k') - lin W a' (gm' k')) := by
      simp_rw [hlin]
      rw [Finset.prod_eq_single k (fun b _ hb => by rw [if_neg hb, zpow_zero]) (by simp)]
      rw [if_pos rfl]
    have e2 : ∏ k', x k' ^ (lin W a (gm' k') - lin W a' (gm' k')) =
        (∏ k', x k' ^ lin W a (gm' k')) / ∏ k', x k' ^ lin W a' (gm' k') := by
      rw [← Finset.prod_div_distrib]
      exact Finset.prod_congr rfl fun k' _ => zpow_sub₀ (hx k') _ _
    rw [e1, e2, eq_div_iff hR0, div_mul_eq_mul_div, div_eq_iff (hP _)]
    rw [hReq, hR'eq] at hrr
    linear_combination hrr
  have hmem : x k ^ p.toNat ∈ k₀ := by
    rw [← zpow_natCast, Int.toNat_of_nonneg hp.le, hxp]
    exact div_mem (mul_mem hr hR') hR
  exact mem_of_pow_mem k₀ hk (x k) p.toNat (by omega) hmem

theorem exists_hasSupports_int (q : ℕ) (φ : InvFun ℤ) (hpol : IsPolFan id q φ) :
    ∃ d, 1 ≤ d ∧ HasSupports (id : ℤ → ℤ) q φ d := by
  refine exists_hasSupports ℤ id q φ hpol fun X _ iM _ _ hX r gm' hgm' => ?_
  obtain rfl : iM = AddCommGroup.toIntModule X := Subsingleton.elim _ _
  have : Module.Free ℤ X := inferInstance
  exact exists_supports_int φ X (hpol X hX) r gm' hgm'

theorem mem_balForms_of_symm {X : Type} [AddCommGroup X] (i : Module ℤ X)
    (β : @LinearMap.BilinForm ℤ _ X _ (AddCommGroup.toIntModule X)) (hs : ∀ y z, β y z = β z y) :
    β ∈ @balForms ℤ _ id X _ i := by
  obtain rfl : i = AddCommGroup.toIntModule X := Subsingleton.elim _ _
  refine ⟨hs, fun a y z => ?_⟩
  simp [map_zsmul]

end GlobalTheory.Poinc.Sep.Assembly

open GlobalTheory.Poinc.Sep.Assembly in

theorem GlobalTheory.Poinc.Sep.sepSt : SepSt := by
  intro g hg n hn hodd F Z z i hTC φ hpol hnsi d J S π j hd hJ hval hbl hji V _ _ _ Q ξ hU m N s ε τ₀ hrk hcone hdef
    hsl hsr hτ K _ _ ev k₀ hk₀ hcen hdefo
  obtain ⟨hproj, hnorm, hoi, hiz, hdense, W, hE8, hTI⟩ := hTC
  haveI := hoi
  let ga : Fin m → LinearMap.BilinForm ℤ Q.X := fun k => (ε (.inl k) : LinearMap.BilinForm ℤ Q.X)
  let t : Fin m → V := fun k => s (.inl k)
  let δ : Fin m → LinearMap.BilinForm ℤ Q.X := fun k => (n : ℤ) • ga k
  have hn0 : (0 : ℤ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsymm : ∀ k a b, δ k a b = δ k b a := fun k a b => by
    simp only [δ, LinearMap.smul_apply, smul_eq_mul]; rw [(hcone.mem k).1 a b]
  have hpsd : ∀ k a, 0 ≤ δ k a a := fun k a => by
    simp only [δ, LinearMap.smul_apply, smul_eq_mul]; exact mul_nonneg hn0.le (hcone.nonneg k a)
  have hposd : ∀ a, a ≠ 0 → ∃ k, 0 < δ k a a := fun a ha => by
    obtain ⟨k, hk⟩ := hdef a ha
    exact ⟨k, by simp only [δ, LinearMap.smul_apply, smul_eq_mul]; exact mul_pos hn0 hk⟩
  have hmono : Q.IsMonomialTau t δ :=
    monoTau_inl Q τ₀ s (fun k => (n : ℤ) • (ε k : LinearMap.BilinForm ℤ Q.X)) hsr hτ
  have hUi : UnifOver F i (ξ ≫ π) Q := hji ▸ unifOver_comp F j π ξ Q hU
  set l := n.minFac with hl_def
  have hl : l.Prime := Nat.minFac_prime (by omega)
  have hldvd : l ∣ n := Nat.minFac_dvd n
  have hlodd : Odd l := Odd.of_dvd_nat hodd hldvd
  have hl3 : 3 ≤ l := by
    have := hl.two_le; obtain ⟨r, hr⟩ := hlodd; omega
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.T.torsion_theta_values_abelianPart_defined_over Q.g l hl hlodd W hE8
  obtain ⟨j₂, hj₂⟩ := GlobalTheory.T.eighthPower_thetaCoefficient_eq_const_mul_monomial Q.g l hl hlodd W hE8
  obtain ⟨jj, X₁, z₁, Φ, y, ρ, e, h, hjj, hTr, hCM⟩ := GlobalTheory.T.exists_fourierTermSystem_regular_traits_given_chart g hg n hn hodd F Z z i hproj ((GlobalTheory.isNormalScheme_iff Z).1 hnorm) hiz hdense W hE8 hTI
    V Q m t δ hrk hsl hsymm hpsd hposd hmono (ξ ≫ π) hUi l hl hldvd (max (max j₁ j₂) 1)
  let e' : Φ.X y ≃ₗ[ℤ] Q.X := e.toIntLinearEquiv
  let ga' : Fin (Φ.m y) → LinearMap.BilinForm ℤ (Φ.X y) := fun k => (LinearMap.BilinForm.congr e'.symm) (ga (h k))
  obtain ⟨ev₁, hev₁, hEl⟩ := GlobalTheory.T.exists_stalk_elements_approx_leadingTerm_quotients g hg n hn hodd F Z z i hproj ((GlobalTheory.isNormalScheme_iff Z).1 hnorm) hiz hdense W hE8 φ d J S π j hJ hval hbl hji
    hpol V Q m t δ hrk hsl hsymm hpsd hposd hmono ga n (by omega) hcone (fun k => rfl) ξ hU ((l ^ jj) ^ 2) X₁ z₁ Φ y ρ e h
    hTr hCM K ev k₀ hk₀ hcen hdefo ga' (fun k a b => by simp [ga', e'])
  obtain ⟨d₀, hd₀, hsup⟩ := exists_hasSupports_int g φ hpol
  have hjj1 : 1 ≤ jj := le_trans (le_max_right _ _) hjj
  have hN₁ : 3 ≤ (l ^ jj) ^ 2 := by
    have h1 : l ≤ l ^ jj := Nat.le_self_pow (by omega) l
    have h2 : l ^ jj ≤ (l ^ jj) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have hm : Φ.mod y = AddCommGroup.toIntModule _ := Subsingleton.elim _ _
  have hrkΦ : Module.finrank ℤ (Φ.X y) ≤ g := by
    convert Φ.rank_le y <;> first | rfl | exact hm.symm
  have hFΦ : IsPolFanOn id φ (Φ.X y) := hpol (Φ.X y) hrkΦ
  have hδ' : ∀ k, Φ.δ y k = (n : ℤ) • ga' k := fun k => by
    ext a b
    rw [(hCM.2.2.2.1 k).2 a b]
    simp [ga', e', δ, ga]
  have hV := GlobalTheory.T.poincareApprox_values_at_point_of_elements ℤ id g φ hpol hnsi d₀ d hd₀ hd hsup 7 W hE8.1 ((l ^ jj) ^ 2) hN₁ _ Φ y ga' n (by omega)
    (isCone_inst (AddCommGroup.toIntModule _) (Φ.mod y) ga' (isCone_equiv hFΦ ga hcone e' h)) hδ' K ev₁ k₀ hEl
  obtain ⟨hinj, -, -, htd, D, e₈, hSharp, hTheta⟩ := hCM
  have hA1 : ∀ i, ev (s (.inl i)) = 0 := fun i => by
    obtain ⟨k, rfl⟩ := h.surjective i
    have := hV.1 k
    rw [(htd k).1, ← RingHom.comp_apply, hev₁] at this
    exact this
  have hlu : IsUnit ((l : ℕ) : Φ.V y) := by
    have hnV : IsUnit ((n : ℕ) : V) := isUnit_natCast_of_cyc n (by omega) V (ξ ≫ π ≫ z)
    have hlV : IsUnit ((l : ℕ) : V) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hldvd) hnV
    simpa using hlV.map ρ
  have hmu : ∀ mu : Fin 8 → Q.X, mono W (Φ.t y) (Φ.δ y) (fun a => e.symm (mu a)) ≠ 0 ∧
      ∃ c, IsUnit (Φ.u y (fun a => e.symm (mu a)) c) := fun mu =>
    ⟨Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (Φ.t_mem y k).2, Φ.u_unit y _⟩
  refine ⟨hA1, ?_, ?_⟩
  · intro o' _ ζ' g' n' F' lam β β₂ hn' hd' hgp hsq hlb a
    have := hj₁ jj (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hjj) V (Φ.V y) (Φ.cn y) hlu Q le_rfl ρ hinj D e₈
      hSharp Φ.Q (fun mu c => Φ.u y (fun a => e.symm (mu a)) c) (fun mu => mono W (Φ.t y) (Φ.δ y) (fun a => e.symm (mu a)))
      hmu hTheta K ev₁ k₀ hk₀ (fun mu c c' hc' => hV.2.1 _ c c' hc') o' ζ' g' n' F' lam β β₂ hn' (by rwa [hev₁]) hgp hsq hlb a
    rwa [hev₁] at this
  · intro W₀ _ ιtb hFB hW₀ i
    rcases i with i | k
    · rw [hA1 i]; exact k₀.zero_mem
    · let u : (Fin 8 → Q.X) → Φ.Q → Φ.V y := fun mu c => Φ.u y (fun a => e.symm (mu a)) c
      let mo : (Fin 8 → Q.X) → Φ.V y := fun mu => mono W (Φ.t y) (Φ.δ y) (fun a => e.symm (mu a))
      let εn : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ Q.X := fun k => (n : ℤ) • (ε k : LinearMap.BilinForm ℤ Q.X)
      have hqnn : ∀ k mu, 0 ≤ qW W (εn (.inl k)) mu := fun k mu => qW_nonneg hE8.1 (hsymm k) (hpsd k) mu
      have hmo : ∀ mu, mo mu = mono W (fun k => ρ (s (.inl k))) (fun k => εn (.inl k)) mu := fun mu => by
        simp only [mo, mono]
        refine Fintype.prod_equiv h _ _ fun k' => ?_
        rw [(htd k').1]
        congr 2
        simp only [qW]
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
        rw [(htd k').2]
        simp [εn, δ, ga]
      have hsb := hj₂ jj (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hjj) V (Φ.V y) (Φ.cn y) hlu Q le_rfl ρ
        hinj D e₈ hSharp Φ.Q u mo hmu hTheta K ev₁ k₀ hk₀ τ₀ m N s εn hsr hqnn hτ hmo W₀ ιtb hFB
        (fun a => by rw [← RingHom.comp_apply, hev₁]; exact hW₀ a)
      obtain ⟨c0, hc0, lam, hlam⟩ := exists_ext_functional (LinearMap.BilinForm ℤ Q.X) (balForms (id : ℤ → ℤ) Q.X)
        (ε.coord (.inr k))
      let lamΦ : LinearMap.BilinForm ℤ (Φ.X y) →ₗ[ℤ] ℤ := lam ∘ₗ (LinearMap.BilinForm.congr e').toLinearMap
      have hback : ∀ β : LinearMap.BilinForm ℤ Q.X,
          LinearMap.BilinForm.congr e' (LinearMap.BilinForm.congr e'.symm β) = β := fun β => by
        ext a b; simp
      have hlamε : ∀ j', lamΦ (LinearMap.BilinForm.congr e'.symm (ε j')) = if j' = .inr k then c0 else 0 := fun j' => by
        simp only [lamΦ, LinearMap.comp_apply, LinearEquiv.coe_coe, hback]
        rw [hlam (ε j'), Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
        split_ifs <;> simp
      have hker : ∀ k', lamΦ (Φ.δ y k') = 0 := fun k' => by
        rw [hδ' k', map_zsmul, show ga' k' = LinearMap.BilinForm.congr e'.symm (ε (.inl (h k'))) from rfl, hlamε]
        simp
      obtain ⟨l1, l1', M, a, a', c, c', hM, hu, hu', hlin, r, hr, hev⟩ := hV.2.2 lamΦ hker
      have hlin' : ∀ k', lin W (fun p => e (a p)) (εn (.inr k')) - lin W (fun p => e (a' p)) (εn (.inr k')) =
          if k' = k then (M : ℤ) * (n * c0) else 0 := fun k' => by
        have hb := (ε (.inr k')).2
        have := hlin _ (mem_balForms_of_symm (Φ.mod y) (LinearMap.BilinForm.congr e'.symm (εn (.inr k'))) fun y z => by
          simp only [LinearMap.BilinForm.congr_apply, LinearEquiv.symm_symm, εn, LinearMap.smul_apply]
          rw [hb.1])
        have htr : ∀ {l2 : ℕ} (b : Fin l2 × Fin 8 → Φ.X y),
            lin W (fun p => e (b p)) (εn (.inr k')) = lin W b (LinearMap.BilinForm.congr e'.symm (εn (.inr k'))) := by
          intro l2 b; simp [lin, qW, e']
        have hl2 : lamΦ (LinearMap.BilinForm.congr e'.symm (εn (.inr k'))) =
            (n : ℤ) * (if (Sum.inr k' : Fin m ⊕ Fin N) = .inr k then c0 else 0) := by
          rw [show εn (.inr k') = (n : ℤ) • (ε (.inr k') : LinearMap.BilinForm ℤ Q.X) from rfl, map_zsmul, map_zsmul,
            hlamε, smul_eq_mul]
        rw [htr, htr, this, hl2]
        rcases eq_or_ne k' k with rfl | hk
        · simp only [if_true]
        · simp only [hk, if_false, Sum.inr.injEq, mul_zero]
      have hxk := mem_of_ratio k₀ hk₀ ev₁ u W (fun k => ev (s (.inr k))) (fun k => ((hsr k).map ev).ne_zero)
        (fun k => εn (.inr k)) (fun mu c => by
          obtain ⟨r, hr, he⟩ := hsb mu c
          refine ⟨r, hr, ?_⟩
          rw [he]
          simp only [← RingHom.comp_apply, hev₁]) (fun p => e (a p)) (fun p => e (a' p)) c c'
        (by
          have hc : (∏ i, u (fun v => e (a (i, v))) (c i)) = Φ.coefT y a c := by simp [u, GlobalTheory.Poinc.VSys.coefT]
          rw [hc]; exact hu) k ((M : ℤ) * (n * c0)) (by positivity) hlin'
        ⟨r, hr, by
          have hc : ∀ {l2 : ℕ} (b : Fin l2 × Fin 8 → Φ.X y) (d : Fin l2 → Φ.Q),
              (∏ i, u (fun v => e (b (i, v))) (d i)) = Φ.coefT y b d := by
            intro l2 b d; simp [u, GlobalTheory.Poinc.VSys.coefT]
          rw [hc, hc]; exact hev⟩
      exact hxk
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartSeparation_data_defined_over_centre_field : GlobalTheory.Poinc.Sep.SepSt := by
  atlas_forward_decl GlobalTheory.Poinc.Sep.sepSt
end
