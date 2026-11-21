import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OneMulConjFracOneEqInvDifferent
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsOActExtendDedekind
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsConjAction
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraSquaredLengthCompPairingHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegersOfCmFieldConjStructure
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsNormalisedPolarisation
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmActionPolarisedCurveAdjointConj

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

private theorem okAct_group_identity {A : Type*} [CommGroup A] (i w : A) (k m n m' n' : ℤ) :
    i ^ (m * m' - n * n' * k) * w ^ (m * n' + n * m' + n * n') =
      (i ^ m * w ^ n) ^ m' * (w ^ m * (w * i ^ (-k)) ^ n) ^ n' := by
  have h1 : m * m' - n * n' * k = m * m' + (-k) * n * n' := by ring
  rw [h1]
  simp only [mul_zpow, ← zpow_mul, zpow_add]
  ac_rfl

theorem exists_okAct_of_equation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (W : G ⟶ G), IsMonHom W → (W ≫ W) * (𝟙 G) ^ ((1 + H.d) / 4) = W → ∃ a : OAct (OK H) G, a.act (wK H) = W ∧ ∀ m n : ℤ, a.act ((m : OK H) + (n : OK H) * wK H) = (𝟙 G) ^ m * W ^ n := by
  intro E _ _ _ H S G _ _ W hW hEq
  obtain ⟨-, hco, -, hsq, -⟩ := OK_isDedekindDomain_and_projective E H
  set k : ℕ := (1 + H.d) / 4 with hk
  choose c hc hcu using hco
  have hcoord : ∀ m n : ℤ, c ((m : OK H) + (n : OK H) * wK H) = (m, n) := fun m n =>
    (hcu _ (m, n) rfl).symm
  have hWW : W ≫ W = W * (𝟙 G) ^ (-(k : ℤ)) := by
    rw [zpow_neg, zpow_natCast, eq_mul_inv_iff_mul_eq]
    exact hEq
  let F : OK H → (G ⟶ G) := fun a => (𝟙 G) ^ (c a).1 * W ^ (c a).2
  have hF : ∀ m n : ℤ, F ((m : OK H) + (n : OK H) * wK H) = (𝟙 G) ^ m * W ^ n := fun m n => by
    simp only [F, hcoord]
  have hex : ∀ a : OK H, ∃ m n : ℤ, a = (m : OK H) + (n : OK H) * wK H := fun a => ⟨_, _, hc a⟩
  refine ⟨⟨F, fun a => ?_, ?_, fun a b => ?_, fun a b => ?_⟩, ?_, hF⟩
  · have h1 := Serre.isMonHom_zpow (𝟙 G) (c a).1
    have h2 := Serre.isMonHom_zpow W (c a).2
    exact Serre.isMonHom_mul _ _
  · have := hF 1 0
    simpa using this
  · obtain ⟨m, n, rfl⟩ := hex a
    obtain ⟨m', n', rfl⟩ := hex b
    have e : ((m : OK H) + (n : OK H) * wK H) * ((m' : OK H) + (n' : OK H) * wK H) =
        ((m * m' - n * n' * (k : ℤ) : ℤ) : OK H) + ((m * n' + n * m' + n * n' : ℤ) : OK H) * wK H := by
      push_cast
      linear_combination ((n : OK H) * (n' : OK H)) * hsq
    rw [e, hF, hF, hF]
    simp only [MonObj.comp_mul, GrpObj.comp_zpow, MonObj.mul_comp, GrpObj.zpow_comp, Category.comp_id,
      Category.id_comp, hWW]
    exact okAct_group_identity _ _ _ _ _ _ _
  · obtain ⟨m, n, rfl⟩ := hex a
    obtain ⟨m', n', rfl⟩ := hex b
    have e : ((m : OK H) + (n : OK H) * wK H) + ((m' : OK H) + (n' : OK H) * wK H) =
        ((m + m' : ℤ) : OK H) + ((n + n' : ℤ) : OK H) * wK H := by
      push_cast
      ring
    rw [e, hF, hF, hF, zpow_add, zpow_add]
    exact mul_mul_mul_comm _ _ _ _
  · have := hF 0 1
    simpa using this

end GlobalTheory.CM
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.exists_cmAdjoin_action_of_equation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (W : G ⟶ G), IsMonHom W → (W ≫ W) * (𝟙 G) ^ ((1 + H.d) / 4) = W → ∃ a : OAct (OK H) G, a.act (wK H) = W ∧ ∀ m n : ℤ, a.act ((m : OK H) + (n : OK H) * wK H) = (𝟙 G) ^ m * W ^ n := by
  atlas_forward_decl GlobalTheory.CM.exists_okAct_of_equation
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.exists_normalized_symmetric_ample_lb : Out.Laws → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : Out.PolAV (Sp R)) (w w' : P.A ⟶ P.A), IsMonHom w → IsMonHom w' → w * w' = 𝟙 P.A → LamEq P.L w (𝟙 P.A) P.L (𝟙 P.A) w' →
  ∃ L' : LB P.A.left, L'.IsLB ∧ Out.Rigidified P.A L' ∧ Out.Sym P.A L' ∧ Out.RelAmple P.A L' ∧ Out.KTriv P.A L' ∧ LamEq L' (𝟙 P.A) (𝟙 P.A) P.L (𝟙 P.A) (𝟙 P.A) ∧ LBIso L' (cubeLB P.A ![𝟙 P.A, w] L') := by
  first | exact @GlobalTheory.CM.exists_normalised_polarisation | exact GlobalTheory.CM.exists_normalised_polarisation | (intros; apply GlobalTheory.CM.exists_normalised_polarisation <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmAction_polarisedCurve_adjoint_conj : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDedekindDomain R] (σ : R →+* ℂ) (P : Out.PolAV (Sp R)) (a : OAct (OK H) P.A), Function.Injective σ → P.g = 1 → ∀ x y : OK H, (y : 𝓞 E) = H.bar x → LamEq P.L (a.act x) (𝟙 P.A) P.L (𝟙 P.A) (a.act y) := by
  first | exact @GlobalTheory.CurveAdjoint.lamEq_act_bar | exact GlobalTheory.CurveAdjoint.lamEq_act_bar | (intros; apply GlobalTheory.CurveAdjoint.lamEq_act_bar <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.EllExists

theorem isQuadLattice_of_linear {g g' : ℕ} (hg : g = 1) (hg' : g' = 1) {Λ : Submodule ℤ (Fin g → ℂ)}
    {Λ' : Submodule ℤ (Fin g' → ℂ)} (hd : DiscreteTopology Λ) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ))
    (hF : ∀ z, z ∈ Λ ↔ F z ∈ Λ') {d : ℕ} {c : ℂ} (hc : c ≠ 0) (h : PureType.IsQuadLattice Λ' d c) :
    ∃ c' : ℂ, c' ≠ 0 ∧ PureType.IsQuadLattice Λ d c' := by
  subst hg hg'
  obtain ⟨a, ha⟩ : ∃ a : ℂ, ∀ z, F z = fun _ => a * z 0 := ⟨F (fun _ => 1) 0, fun z => by
    have e : z = z 0 • fun _ => (1 : ℂ) := by
      funext i
      fin_cases i
      simp
    funext i
    fin_cases i
    conv_lhs => rw [e, map_smul]
    simp [mul_comm]⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    have ht : (Λ : Set (Fin 1 → ℂ)) = Set.univ := Set.eq_univ_of_forall fun z => (hF z).2 (by
      rw [ha]
      simp only [zero_mul]
      exact Λ'.zero_mem)
    have h1 : IsDiscrete (Λ : Set (Fin 1 → ℂ)) := ⟨hd⟩
    rw [ht, isDiscrete_univ_iff] at h1
    have := (isClopen_discrete ({0} : Set (Fin 1 → ℂ))).eq_univ ⟨0, rfl⟩
    have h2 : (1 : Fin 1 → ℂ) ∈ ({0} : Set (Fin 1 → ℂ)) := this ▸ Set.mem_univ _
    exact one_ne_zero h2
  refine ⟨c / a, div_ne_zero hc ha0, fun z => ?_⟩
  rw [hF, h, ha]
  refine exists₂_congr fun m n => ⟨fun e => ?_, fun e => ?_⟩
  · funext i
    fin_cases i
    have := congrFun e 0
    field_simp
    field_simp at this
    simpa [mul_comm a] using this
  · funext i
    rw [e]
    field_simp

theorem isQuadLattice_of_isGrpPullback (hU : ThetaUnifAV) (hL : Out.Laws) {R : Type} [CommRing R]
    (P : Out.PolAV (Sp R)) (hg : P.g = 1) (σ : R →+* ℂ) {d : ℕ}
    (h : ∀ (Q : Out.PolAV (Sp ℂ)) (φ : Q.A.left ⟶ P.A.left), IsPolFibre σ P Q φ → ∀ u : HolUnif Q.A Q.L Q.g,
      ∃ c : ℂ, c ≠ 0 ∧ PureType.IsQuadLattice u.Λ d c)
    (Q : Out.PolAV (Sp ℂ)) (hQ : Q.g = 1) (φ : Q.A.left ⟶ P.A.left) (hφ : IsGrpPullback Q.A P.A (spMap σ) φ)
    (u : HolUnif Q.A Q.L Q.g) : ∃ c : ℂ, c ≠ 0 ∧ PureType.IsQuadLattice u.Λ d c := by
  obtain ⟨Q₀, φ₀, h₀⟩ := exists_isPolFibre hL.polBaseChange σ P
  obtain ⟨rig, hrig⟩ := Q₀.rigid
  obtain ⟨u₀, -, -, -, -, -, t₁, t₂, -⟩ := hU Q₀ rig hrig
  obtain ⟨c, hc, hΛ⟩ := h Q₀ φ₀ h₀ u₀
  obtain ⟨f, hf, ef⟩ := NormHom.exists_monHom_lift hφ h₀.2.1 (𝟙 P.A)
  obtain ⟨F, hF, hF', -⟩ :=
    HomLinear.exists_linear_of_isMonHom Q.A Q₀.A Q.isAb Q₀.isAb Q.L Q₀.L Q.g Q₀.g u u₀ t₁ t₂ f hf
  refine isQuadLattice_of_linear hQ (h₀.1.trans hg) u.discrete F (fun z => ⟨hF' z, fun hz => ?_⟩) hc hΛ
  rw [← u₀.ker, hF] at hz
  rw [← u.ker]
  apply NormHom.push_inj hφ
  have e := NormHom.push_comp hφ h₀.2.1 ef (u.ex z)
  rw [hz, map_one, Category.comp_id] at e
  rw [map_one, e]

theorem exists_ell_pos (hC : CMCurve) (hU : ThetaUnifAV) (hL : Out.Laws) (hX : HomExtDvr) {E : Type} [Field E]
    [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] {χ : DirichletCharacter ℂ H.d} (hχ : IsKroneckerChar χ) :
    ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M) (ω : 𝓞 M) (C : Ell H (𝓞 M) ω) (x : ℝ),
      ((ω : M) : ℂ) = (1 + Complex.I * √H.d) / 2 ∧ C.IsPrincipalAt ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) ∧
      C.HasPeriod x ∧ (x : ℂ) = (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √H.d) : ℝ) -
        deriv χ.LFunction 1 / χ.LFunction 1 := by
  have hm := H.d_mod
  obtain ⟨K, _, h2, hr⟩ := exists_quadraticField_sq_eq_neg (d := H.d) (by omega)
  obtain ⟨M, _, w, P, v, hw, hg, hv, ⟨P₀, φ, v₀, W, hφ, hv₀, hb₀, hW, hWW, hWv⟩, hΛ, n, hn0, hn, hx, -⟩ :=
    chowla_selberg_lie_lines hC (by omega) H.d_prime.squarefree (by omega) h2 hr hχ
  have := P₀.isAb.comm
  have := P.isAb.comm
  obtain ⟨a₀, ha₀, -⟩ := GlobalTheory.T.exists_cmAdjoin_action_of_equation E H _ P₀.A W hW hWW
  obtain ⟨a, ha⟩ := exists_oAct_extend_dedekind hX (𝓞 M) M (OK H) P.A P₀.A φ P.isAb hφ.2.1 a₀
  have hvt : IsTangent v := hv.1 0
  have := a.hom (wK H)
  obtain ⟨c, hc, -⟩ := hv.2 _ (HomLinear.isTangent_comp (a.act (wK H)) hvt)
  obtain ⟨ω, rfl⟩ : ∃ ω, c = ![ω] := ⟨c 0, by funext i; fin_cases i; rfl⟩
  have hc₀ := (lieComb_baseChange _ _ (algebraMap (𝓞 M) M) P.A P₀.A φ hφ.2.1 1 ![v] _ ![ω] ![v₀] (v₀ ≫ W)
    (fun j => by fin_cases j; exact hv₀) hc).1 (NormHom.isVecOver_comp hv₀ (ha₀ ▸ ha (wK H)))
  have hω : (ω : M) = w := congrFun ((hb₀.2 _ (HomLinear.isTangent_comp W (hb₀.1 0))).unique hc₀ hWv) 0
  have hσ : Function.Injective ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) :=
    (algebraMap M ℂ).injective.comp (IsFractionRing.injective (𝓞 M) M)
  obtain ⟨L', h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := GlobalTheory.T.exists_normalized_symmetric_ample_lb hL (𝓞 M) P (a.act (wK H)) (a.act (EllConj.barK H (wK H)))
    (a.hom _) (a.hom _) (by rw [← a.add, add_comm, EllConj.barK_wK_add, a.one])
    (GlobalTheory.T.cmAction_polarisedCurve_adjoint_conj hU hL E H (𝓞 M) _ P a hσ hg _ _ rfl)
  let P' : Out.PolAV (Sp (𝓞 M)) := ⟨P.A, P.isAb, P.g, P.smoothDim, L', h₁, h₂, h₃, h₄, h₅⟩
  have key : ∀ (s : M →+* ℂ) r, IsLieNormSq P' v (s.comp (algebraMap (𝓞 M) M)) r → r = n s := fun s r h => by
    have h1 : IsLieComb ![(1 : 𝓞 M)] ![v] (v ≫ 𝟙 P.A) := by
      rw [LieComb.isLieComb_iff_tanExp, Category.comp_id]
      have e : (![1] : Fin 1 → 𝓞 M) = Pi.single 0 1 := by
        funext i
        fin_cases i
        simp
      rw [e]
      exact (LieComb.tanExp_single hv.1 0).symm
    have e := NormHom.lieNormSq_comp hU hL (𝓞 M) P P' (𝟙 P.A) (𝟙 P.A) v 1 _ (n s) r inferInstance inferInstance h₆ hvt
      h1 ((hn s _).2 rfl) (by rwa [Category.comp_id])
    simpa using e
  refine ⟨M, inferInstance, ω, ⟨P', hg, a, v, hv, hc, GlobalTheory.T.cmAction_polarisedCurve_adjoint_conj hU hL E H (𝓞 M) _ P' a hσ hg, h₇⟩, -meanLog M n,
    hω ▸ hw, fun Q ψ hψ u => ?_, ⟨n, fun s => ⟨hn0 s, fun r => ⟨key s r, fun e => ?_⟩⟩, rfl⟩, hx⟩
  · refine isQuadLattice_of_isGrpPullback hU hL P hg _ (fun Q ψ hψ u => ?_) Q (hψ.1.trans hg) ψ hψ.2.1 u
    obtain ⟨c, hc, h⟩ := hΛ Q ψ hψ u
    rw [hw] at h
    exact ⟨c, hc, h⟩
  · obtain ⟨r', hr'⟩ := exists_isLieNormSq hU hL.polBaseChange P' hvt (s.comp (algebraMap (𝓞 M) M))
    rwa [e, ← key s r' hr']

theorem exists_ell : CMCurve → ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ ρ : ℂ, ρ ^ 2 = -(H.d : ℂ) → ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M) (ω : 𝓞 M) (C : Ell H (𝓞 M) ω) (x : ℝ), 2 * ((ω : M) : ℂ) - 1 = ρ ∧ C.IsPrincipalAt ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) ∧ C.HasPeriod x ∧ (x : ℂ) = (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √H.d) : ℝ) - deriv χ.LFunction 1 / χ.LFunction 1 := by
  intro hC hU hL hX E _ _ _ H _ χ hχ ρ hρ
  obtain ⟨M, _, ω, C, x, hω, hp, hx, hv⟩ := exists_ell_pos hC hU hL hX H hχ
  have e : ρ ^ 2 = (Complex.I * √H.d) ^ 2 := by
    rw [hρ, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 e with rfl | rfl
  · exact ⟨M, inferInstance, ω, C, x, by rw [hω]; ring, hp, hx, hv⟩
  · obtain ⟨a, -, h₁, h₂, h₃⟩ := EllConj.exists_conj_action E H (𝓞 M) ω C
    refine ⟨M, inferInstance, 1 - ω, ⟨C.P, C.dim, a, C.v, C.basis, h₁, h₂, h₃⟩, x, ?_, hp, hx, hv⟩
    have : (((1 - ω : 𝓞 M) : M) : ℂ) = 1 - ((ω : M) : ℂ) := by simp
    rw [this, hω]
    ring

end GlobalTheory.CM.EllExists
end
end
