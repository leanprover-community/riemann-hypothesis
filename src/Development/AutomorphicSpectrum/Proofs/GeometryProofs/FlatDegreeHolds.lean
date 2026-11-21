import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.HermitianMetricLogNormFormula
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GramDetNeZeroLocalBasisCofinite
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveZNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodReductionModelCmPeriodFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmExistsClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogNormsExtDegreeAdelic
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCmPeriodEmbedding
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackPureFrameOpen
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocalBasisGramDetLogNorm
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionCmHeight
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.ExistsExtensionEmbeddingAlgClosed
import Development.WeilBound.CoreStatements.SesquilinearFractions.LieNormSquareOfFamily
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramLinearCombination
import Development.WeilBound.CoreStatements.SesquilinearFractions.GGramPush
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SesqSesquilinearSkewHermitian
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsAlt

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem exists_curve0_hasPeriod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d]
    (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ ρ : ℂ, ρ ^ 2 = -(H.d : ℂ) →
    ∃ (Z : Curve0 H ρ) (x : ℝ), Z.z ≠ 0 ∧ Z.C.HasPeriod x ∧
      (x : ℂ) = (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √H.d) : ℝ) -
        deriv χ.LFunction 1 / χ.LFunction 1 := by
  intro E _ _ _ H _ χ hχ ρ hρ
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  have hU := GlobalTheory.thetaUnifAV_closed
  have hX := GlobalTheory.CM.homExtDvr_of_card_torsion GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional
  obtain ⟨M, _, ω, C, x, hω, hpr, hper, hx⟩ := GlobalTheory.T.exists_cmEllipticCurve_integers_with_period GlobalTheory.T.exists_cmEllipticCurve_withPeriod hU hL hX E H χ hχ ρ hρ
  obtain ⟨C', π, c'⟩ := exists_ellMap hL.polBaseChange E H _ ω C ℂ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))
  obtain ⟨u, hu⟩ := PureType.exists_isThetaUnif hU C'.P
  obtain ⟨c, hc, hΛ⟩ := hpr C'.P π c'.2.1 u
  obtain ⟨Hm, χ', Ef, h1, h2, h3⟩ := id hu
  obtain ⟨w, hw, -⟩ := h2 C'.v (C'.basis.1 0)
  have hd := C'.dim
  let Z : Curve0 H ρ := ⟨M, ω, C, hω, C', π, c', u, hu, c, hc, hΛ, w ⟨0, by omega⟩ / c, by
    convert hw using 1
    funext j
    rw [mul_div_cancel₀ _ hc]
    congr 1
    apply Fin.ext
    have := j.2
    simp only
    omega⟩
  exact ⟨Z, x, GlobalTheory.T.curve_z_ne_zero E H ρ Z, hper, hx⟩

end GlobalTheory.CompanionTheory.Ar.Fl
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chowla_selberg_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ ρ : ℂ, ρ ^ 2 = -(H.d : ℂ) → ∃ (Z : Curve0 H ρ) (x : ℝ), Z.z ≠ 0 ∧ Z.C.HasPeriod x ∧ (x : ℂ) = (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √H.d) : ℝ) - deriv χ.LFunction 1 / χ.LFunction 1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Fl.exists_curve0_hasPeriod
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.ConstAlg

theorem finite_fieldRange {E : Type} [Field E] [NumberField E] (τ : E →+* ℂ) :
    FiniteDimensional ℚ τ.toRatAlgHom.fieldRange :=
  (AlgEquiv.ofInjectiveField τ.toRatAlgHom).toLinearEquiv.finiteDimensional

theorem const_algebraic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty)
    (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c)
    (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 →
    (∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P →
      y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U) →
    IsLineFn U τ φ → LinearIndependent (𝓞 E) e → IsConstMul U τ φ FU i e ρ →
    ∃ (k : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ k) (r : k), c.F ≤ k ∧ (∀ b, (Z b).M ≤ k) ∧ r ≠ 0 ∧
      (r : ℂ) * (Z true).z ^ D.p = ρ * (Z false).z ^ D.q := by
  intro E _ _ _ H D l Xo c g ty FU i Z U τ φ e ρ hty hrt hmem hline he hconst
  obtain ⟨P, hP, x, hx, X, v, w, hk, hloc, hfr⟩ :=
    GlobalTheory.T.exists_cm_period_embedding E H D l Xo c g ty FU i Z τ ⟨2, Nat.prime_two⟩ τ.toRatAlgHom.fieldRange (finite_fieldRange τ) hty hrt
  have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
    simp [(FU.sig i).1, (FU.sig i).2]
  obtain ⟨T, hT, -, hdet, -⟩ := GlobalTheory.T.exists_transition_matrix_gram E H (FU.Di i) _ x e hcard he
  have hT0 : T.det ≠ 0 := hdet hloc.1
  have horth : ∀ a b, sesq (FU.Di i) (x (.inl a)) (x (.inr b)) = 0 := fun a b =>
    (GlobalTheory.T.pure_type_lattices_orthogonal E H (FU.Di i) g ty P hP _ _ (hx.1 a) (hx.2 b)).1
  have hG0 := (GlobalTheory.T.local_basis_gram_det_log_norm E H (FU.Di i) D.p D.q x ⟨2, Nat.prime_two⟩ hloc horth).1
  obtain ⟨hfm, hval⟩ := GlobalTheory.T.cm_pack_pure_frame_open E H D l Xo c g ty FU i Z P hP X x hx U τ φ e ρ T v w hty hrt hmem hline he
    hconst hloc.1 hT hfr
  have hφ : φ X.K X.y v w ≠ 0 := hline.ne X.K X.β X.y v w hfm
  have hmemK : ∀ t : E, τ t ∈ X.K := fun t => hk (τ.toRatAlgHom.mem_fieldRange.2 ⟨t, rfl⟩)
  set G := gramE (FU.Di i) (x ∘ Sum.inr) with hGdef
  let a : X.K := ⟨τ T.det, hmemK _⟩
  let b : X.K := ⟨τ G.det, hmemK _⟩
  have ha : a ≠ 0 := fun h => hT0 ((map_eq_zero τ).1 (congrArg Subtype.val h))
  have hb : b ≠ 0 := fun h => hG0 ((map_eq_zero τ).1 (congrArg Subtype.val h))
  have hbC : τ G.det ≠ 0 := (map_ne_zero τ).2 hG0
  refine ⟨X.K, inferInstance, φ X.K X.y v w * a / b, X.hc, X.hM, div_ne_zero (mul_ne_zero hφ ha) hb, ?_⟩
  have hcoe : ((φ X.K X.y v w * a / b : X.K) : ℂ) = ((φ X.K X.y v w : X.K) : ℂ) * τ T.det / τ G.det := rfl
  rw [hcoe]
  field_simp
  linear_combination hval

end GlobalTheory.CompanionTheory.Ar.Fl.ConstAlg
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_function_cm_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → (∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P → y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U) → IsLineFn U τ φ → LinearIndependent (𝓞 E) e → IsConstMul U τ φ FU i e ρ → ∃ (k : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ k) (r : k), c.F ≤ k ∧ (∀ b, (Z b).M ≤ k) ∧ r ≠ 0 ∧ (r : ℂ) * (Z true).z ^ D.p = ρ * (Z false).z ^ D.q := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Fl.ConstAlg.const_algebraic
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.lie_norm_square_of_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (T : PAT H (Sp R)) (h : D.La → D.La → OK H) (L : Submodule (𝓞 E) D.La) (ψ : L → (C.P.A ⟶ T.t.G)) (σ : R →+* ℂ) (κ : OK H →+* ℂ) (r : ℝ) (n : ℕ) (a : Fin n → L) (u : Fin n → (epsAt (spMap σ) ⟶ T.t.G)), IsFam C T h L ψ → κ (wK H) = σ ω → IsLieNormSq C.P C.v σ r → (∀ k, (u k).left = spMap (dualMap σ) ≫ C.v.left ≫ (ψ (a k)).left) → IsHodgeGram T.t.G T.t.PP.L (spMap σ) u (Matrix.of fun k k' => r * κ (h (a k) (a k'))) := by
  first | exact @PositivityTheory.Xgf.lie_norm_square_of_family | exact PositivityTheory.Xgf.lie_norm_square_of_family
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_norm_square_of_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (T : PAT H (Sp R)) (h : D.La → D.La → OK H) (L : Submodule (𝓞 E) D.La) (ψ : L → (C.P.A ⟶ T.t.G)) (σ : R →+* ℂ) (κ : OK H →+* ℂ) (r : ℝ) (n : ℕ) (a : Fin n → L) (u : Fin n → (epsAt (spMap σ) ⟶ T.t.G)), IsFam C T h L ψ → κ (wK H) = σ ω → IsLieNormSq C.P C.v σ r → (∀ k, (u k).left = spMap (dualMap σ) ≫ C.v.left ≫ (ψ (a k)).left) → IsHodgeGram T.t.G T.t.PP.L (spMap σ) u (Matrix.of fun k k' => r * κ (h (a k) (a k'))) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.lie_norm_square_of_family
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.hodge_gram_invariant_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f) (x' : Sp ℂ ⟶ S') (x : Sp ℂ ⟶ S) (n : ℕ) (v' : Fin n → (epsAt x' ⟶ t'.G)) (v : Fin n → (epsAt x ⟶ t.G)) (Γ : Matrix (Fin n) (Fin n) ℂ), x = x' ≫ f → (∀ k, (v k).left = (v' k).left ≫ m.φ) → (IsHodgeGram t'.G t'.PP.L x' v' Γ ↔ IsHodgeGram t.G t.PP.L x v Γ) := by
  first | exact @PositivityTheory.Xgf.hodge_gram_invariant_pullback | exact PositivityTheory.Xgf.hodge_gram_invariant_pullback
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_gram_invariant_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f) (x' : Sp ℂ ⟶ S') (x : Sp ℂ ⟶ S) (n : ℕ) (v' : Fin n → (epsAt x' ⟶ t'.G)) (v : Fin n → (epsAt x ⟶ t.G)) (Γ : Matrix (Fin n) (Fin n) ℂ), x = x' ≫ f → (∀ k, (v k).left = (v' k).left ≫ m.φ) → (IsHodgeGram t'.G t'.PP.L x' v' Γ ↔ IsHodgeGram t.G t.PP.L x v Γ) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.hodge_gram_invariant_pullback
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.KForm

section Embeddings

variable {E : Type} [Field E] [NumberField E]

open Classical in

theorem sum_dual_mul (σ τ : E →+* ℂ) :
    ∑ k, σ (HT.dualInt E k) * τ ((RingOfIntegers.basis E k : 𝓞 E) : E) = if τ = σ then 1 else 0 := by
  let ρ : 𝓞 E →+* Module.End ℂ ℂ :=
    (Algebra.lmul ℂ ℂ).toRingHom.comp (τ.comp (algebraMap (𝓞 E) E))
  have hρ : ∀ (a : 𝓞 E) (z : ℂ), ρ a z = τ (a : E) * z := fun a z => rfl
  have hmem : (1 : ℂ) ∈ HT.eigSp ρ τ := HT.LatBasic.mem_eigSp.2 fun a => by
    rw [hρ, smul_eq_mul]
  have hP : HT.eigProj ρ σ 1 =
      ∑ k, σ (HT.dualInt E k) * τ ((RingOfIntegers.basis E k : 𝓞 E) : E) := by
    simp [HT.eigProj, LinearMap.sum_apply, hρ]
  rw [← hP]
  split_ifs with h
  · subst h
    exact HT.LatBasic.eigProj_of_mem hmem
  · exact HT.LatBasic.eigProj_of_ne (Ne.symm h) hmem

theorem trace_cast (z : E) :
    ((Algebra.trace ℚ E z : ℚ) : ℂ) = ∑ τ : E →ₐ[ℚ] ℂ, τ z := by
  have := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := z)
  simpa using this

end Embeddings

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem kappa_form {ε : ℤˣ} {h : D.La → D.La → OK H} {σ : E →+* ℂ} {κ : OK H →+* ℂ}
    (hh : IsKForm D ε h) (hκ : κ (wK H) = σ (H.w0 : E)) (X Y : D.La) :
    κ (h X Y) = ((ε : ℤ) : ℂ) *
      ∑ τ : E →ₐ[ℚ] ℂ, τ (sesq D X Y) * (τ (H.w0 : E) - 1 + σ (H.w0 : E)) := by
  obtain ⟨hT, -⟩ := GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D
  have e1 : h X Y = (((ε : ℤ) * (D.EF (H.w0 • X) Y - D.EF X Y) : ℤ) : OK H) +
      (((ε : ℤ) * D.EF X Y : ℤ) : OK H) * wK H := by
    apply Subtype.ext
    simpa [wK] using hh X Y
  have t1 : ((D.EF (H.w0 • X) Y : ℤ) : ℂ) =
      ∑ τ : E →ₐ[ℚ] ℂ, τ (H.w0 : E) * τ (sesq D X Y) := by
    have := congrArg (fun q : ℚ => (q : ℂ)) (hT H.w0 X Y)
    simp only [trace_cast, map_mul] at this
    rw [this]
    simp
  have t0 : ((D.EF X Y : ℤ) : ℂ) = ∑ τ : E →ₐ[ℚ] ℂ, τ (sesq D X Y) := by
    have h1 : Algebra.trace ℚ E (sesq D X Y) = (D.EF X Y : ℚ) := by simpa using hT 1 X Y
    rw [← trace_cast, h1]
    simp
  have hs : ∑ τ : E →ₐ[ℚ] ℂ, τ (sesq D X Y) * (τ (H.w0 : E) - 1 + σ (H.w0 : E)) =
      ∑ τ : E →ₐ[ℚ] ℂ, τ (H.w0 : E) * τ (sesq D X Y) - ∑ τ : E →ₐ[ℚ] ℂ, τ (sesq D X Y) +
        (∑ τ : E →ₐ[ℚ] ℂ, τ (sesq D X Y)) * σ (H.w0 : E) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun τ _ => by ring
  rw [e1, map_add, map_mul, map_intCast, map_intCast, hκ, hs]
  push_cast
  rw [t1, t0]
  ring

theorem sigma_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H) (σ : E →+* ℂ) (κ : OK H →+* ℂ) (n : ℕ) (e : Fin n ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (x y : D.La), IsKForm D ε h → κ (wK H) = σ (H.w0 : E) → ∑ k, ∑ k', σ (HT.dualInt E (e k)) * κ (h (RingOfIntegers.basis E (e k) • x) (RingOfIntegers.basis E (e k') • y)) * starRingEnd ℂ (σ (HT.dualInt E (e k'))) = ((ε : ℤ) : ℂ) * σ ((H.rt : E) * sesq D x y) := by
  classical
  intro E _ _ _ H D ε h σ κ n e x y hh hκ
  obtain ⟨-, -, -, hL, hR, -⟩ := GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D

  have hform : ∀ a c : 𝓞 E, κ (h (a • x) (c • y)) = ((ε : ℤ) : ℂ) *
      ∑ τ : E →ₐ[ℚ] ℂ, τ (a : E) * starRingEnd ℂ (τ (c : E)) *
        (τ (sesq D x y) * (τ (H.w0 : E) - 1 + σ (H.w0 : E))) := by
    intro a c
    rw [kappa_form hh hκ]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => ?_
    have hc : τ (IsCMField.complexConj E (c : E)) = starRingEnd ℂ (τ (c : E)) :=
      IsCMField.complexEmbedding_complexConj E (τ : E →+* ℂ) (c : E)
    rw [hL, hR, map_mul, map_mul, hc]
    ring

  set S : (E →ₐ[ℚ] ℂ) → ℂ := fun τ =>
    ∑ k : Fin n, σ (HT.dualInt E (e k)) * τ ((RingOfIntegers.basis E (e k) : 𝓞 E) : E) with hSdef
  have hS : ∀ τ : E →ₐ[ℚ] ℂ, S τ = if (τ : E →+* ℂ) = σ then 1 else 0 := by
    intro τ
    have := sum_dual_mul σ (τ : E →+* ℂ)
    rw [← Equiv.sum_comp e] at this
    exact this
  set c : (E →ₐ[ℚ] ℂ) → ℂ := fun τ =>
    τ (sesq D x y) * (τ (H.w0 : E) - 1 + σ (H.w0 : E)) with hcdef
  have hexp : ∑ k, ∑ k', σ (HT.dualInt E (e k)) *
        κ (h (RingOfIntegers.basis E (e k) • x) (RingOfIntegers.basis E (e k') • y)) *
        starRingEnd ℂ (σ (HT.dualInt E (e k'))) =
      ((ε : ℤ) : ℂ) * ∑ τ : E →ₐ[ℚ] ℂ, S τ * starRingEnd ℂ (S τ) * c τ := by
    simp only [hform, hSdef, hcdef, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hexp, Finset.sum_eq_single σ.toRatAlgHom]
  · have h1 : S σ.toRatAlgHom = 1 := by
      rw [hS]
      exact if_pos (RingHom.ext fun _ => rfl)
    have h2 : σ (H.rt : E) = 2 * σ (H.w0 : E) - 1 := by
      have h3 := congrArg (fun a : 𝓞 E => σ (algebraMap (𝓞 E) E a)) H.two_weight_eq_one_add_root
      simp only [map_mul, map_add, map_one, map_ofNat] at h3
      rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap]
      linear_combination -h3
    rw [h1, map_one, map_mul, h2]
    simp only [hcdef]
    change _ * (1 * 1 * (σ (sesq D x y) * (σ (H.w0 : E) - 1 + σ (H.w0 : E)))) = _
    ring
  · intro τ _ hτ
    have h0 : S τ = 0 := by
      rw [hS]
      refine if_neg fun hc => hτ (AlgHom.ext fun z => ?_)
      exact congrArg (fun f : E →+* ℂ => f z) hc
    rw [h0]
    simp
  · intro hn
    exact absurd (Finset.mem_univ _) hn

end GlobalTheory.CompanionTheory.Ar.Fl.KForm
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_basis_hermitian_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H) (σ : E →+* ℂ) (κ : OK H →+* ℂ) (n : ℕ) (e : Fin n ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (x y : D.La), IsKForm D ε h → κ (wK H) = σ (H.w0 : E) → ∑ k, ∑ k', σ (HT.dualInt E (e k)) * κ (h (RingOfIntegers.basis E (e k) • x) (RingOfIntegers.basis E (e k') • y)) * starRingEnd ℂ (σ (HT.dualInt E (e k'))) = ((ε : ℤ) : ℂ) * σ ((H.rt : E) * sesq D x y) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Fl.KForm.sigma_component
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem lieNormSq_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [CommRing R'] (ω : R) (ω' : R') (C : Ell H R ω) (C' : Ell H R' ω') (f : R →+* R') (φ : C'.P.A.left ⟶ C.P.A.left) (σ : R' →+* ℂ) (r : ℝ), EllMap C' C f φ → (IsLieNormSq C.P C.v (σ.comp f) r ↔ IsLieNormSq C'.P C'.v σ r) := by
  intro E _ _ _ H R R' _ _ ω ω' C C' f φ σ r h
  exact (GlobalTheory.CM.EllComp.isLieNormSq_iff h.2.1 h.2.2.1 σ r).symm

end GlobalTheory.CompanionTheory.Ar.Fl
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_norm_sq_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [CommRing R'] (ω : R) (ω' : R') (C : Ell H R ω) (C' : Ell H R' ω') (f : R →+* R') (φ : C'.P.A.left ⟶ C.P.A.left) (σ : R' →+* ℂ) (r : ℝ), EllMap C' C f φ → (IsLieNormSq C.P C.v (σ.comp f) r ↔ IsLieNormSq C'.P C'.v σ r) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Fl.lieNormSq_baseChange
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Fl.GInf

variable {S : Scheme.{0}} {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

theorem dualMap_comp_alg (f : R →+* R') :
    (dualMap f).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp f := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_comp_epsMul (f : R →+* R') (c : R) :
    (dualMap f).comp (epsMul c) = (epsMul (f c)).comp (dualMap f) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, epsMul, mul_comm]

theorem fst_comp_dualMap (f : R →+* R') :
    (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (dualMap f) = f.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => ?_
  simp [dualMap]

theorem dualMap_comp_dualMap (f : R →+* R') (g : R' →+* R'') :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap]

theorem epsMul_zero_eq : epsMul (0 : R) =
    (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

def bar (f : R →+* R') (x : Sp R ⟶ S) : epsAt (spMap f ≫ x) ⟶ epsAt x :=
  Over.homMk (spMap (dualMap f)) (by
    show spMap (dualMap f) ≫ spMap (algebraMap R (DualNumber R)) ≫ x = spMap (algebraMap R' (DualNumber R')) ≫ spMap f ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_alg])

theorem exists_bc {G : Over S} (f : R →+* R') (x : Sp R ⟶ S) {x' : Sp R' ⟶ S} (hx : x' = spMap f ≫ x)
    (u : epsAt x ⟶ G) : ∃ u' : epsAt x' ⟶ G, u'.left = spMap (dualMap f) ≫ u.left := by
  subst hx
  exact ⟨bar f x ≫ u, rfl⟩

theorem isComb_bc {G : Over S} [GrpObj G] (f : R →+* R') (x : Sp R ⟶ S) {x' : Sp R' ⟶ S} (hx : x' = spMap f ≫ x)
    {n : ℕ} (c : Fin n → R)
    (v : Fin n → (epsAt x ⟶ G)) (w : epsAt x ⟶ G) (v' : Fin n → (epsAt x' ⟶ G))
    (w' : epsAt x' ⟶ G) (hv : ∀ i, (v' i).left = spMap (dualMap f) ≫ (v i).left)
    (hw : w'.left = spMap (dualMap f) ≫ w.left) (h : Fl.IsComb c v w) :
    Fl.IsComb (fun i => f (c i)) v' w' := by
  subst hx
  obtain ⟨u, hu, rfl⟩ := h
  let φ : (epsAt x ⟶ G) →* (epsAt (spMap f ≫ x) ⟶ G) :=
    { toFun := fun y => bar f x ≫ y
      map_one' := comp_one _
      map_mul' := fun a b => comp_mul _ _ _ }
  refine ⟨fun i => φ (u i), fun i => ?_, ?_⟩
  · show spMap (dualMap f) ≫ (u i).left = _
    rw [hu i, hv i, ← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_epsMul]
  · have e : w' = φ (List.ofFn u).prod := Over.OverMorphism.ext hw
    rw [e, map_list_prod, List.map_ofFn]
    rfl

theorem one_left {G : Over S} [GrpObj G] {T : Scheme.{0}} (x : T ⟶ S) : (1 : Over.mk x ⟶ G).left = x ≫ eSec G := by
  rw [Hom.one_def, Over.comp_left]
  rfl

theorem isComb_pad {G : Over S} [GrpObj G] [IsCommMonObj G] {x : Sp R ⟶ S} {m M : ℕ} {c : Fin m → R}
    {v : Fin m → (epsAt x ⟶ G)} {w : epsAt x ⟶ G} (C : Fin M → R) (V : Fin M → (epsAt x ⟶ G)) (jj : Fin m → Fin M)
    (hj : Function.Injective jj) (hc : ∀ j, C (jj j) = c j) (hv : ∀ j, V (jj j) = v j)
    (h0 : ∀ q, q ∉ Set.range jj → C q = 0) (ht : ∀ q, IsTanAt G x (V q)) (h : Fl.IsComb c v w) :
    Fl.IsComb C V w := by
  classical
  obtain ⟨u, hu, rfl⟩ := h
  let U : Fin M → (epsAt x ⟶ G) := fun q => if hq : ∃ j, jj j = q then u hq.choose else 1
  have hU : ∀ j, U (jj j) = u j := fun j => by
    have hq : ∃ j', jj j' = jj j := ⟨j, rfl⟩
    simp only [U, dif_pos hq]
    rw [hj hq.choose_spec]
  have hU1 : ∀ q, q ∉ Set.range jj → U q = 1 := fun q hq => by
    simp only [U]
    exact dif_neg hq
  refine ⟨U, fun q => ?_, ?_⟩
  · by_cases hq : q ∈ Set.range jj
    · obtain ⟨j, rfl⟩ := hq
      rw [hU, hu, hc, hv]
    · rw [hU1 q hq, h0 q hq, epsMul_zero_eq, ← spMap_comp_spMap, Category.assoc]
      have := ht q
      unfold IsTanAt at this
      erw [this]
      rw [one_left, one_left]
      rfl
  · rw [List.prod_ofFn, List.prod_ofFn]
    exact Fintype.prod_of_injective jj hj _ _ (fun q hq => hU1 q hq) (fun j => (hU j).symm)

end GlobalTheory.CompanionTheory.Ar.Fl.GInf

namespace GlobalTheory.CompanionTheory.Ar.Fl.GInf

variable {S : Scheme.{0}} {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem tan_iff {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {x' : Sp R ⟶ S'} {x : Sp R ⟶ S} (hx : x = x' ≫ f) (v' : epsAt x' ⟶ t'.G) (v : epsAt x ⟶ t.G)
    (h : v.left = v'.left ≫ m.φ) : IsTanAt t'.G x' v' ↔ IsTanAt t.G x v := by
  subst hx
  have he : eSec t'.G ≫ m.φ = f ≫ eSec t.G := PolBaseChange.eSec_comm m.cart
  unfold IsTanAt
  rw [one_left, one_left, h]
  constructor
  · intro e
    rw [← Category.assoc, e, Category.assoc, he, Category.assoc]
  · intro e
    refine m.cart.1.hom_ext ?_ ?_
    · have he' : eSec t'.G ≫ m.cm.F = f ≫ eSec t.G := he
      rw [Category.assoc, e, Category.assoc, Category.assoc, he']
    · have h1 : v'.left ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x' := Over.w v'
      have h2 : eSec t'.G ≫ t'.G.hom = 𝟙 _ := Over.w η[t'.G]
      rw [Category.assoc, Category.assoc, h1, h2]
      refine Eq.trans ?_ (Category.comp_id x').symm
      erw [← Category.assoc, spMap_comp_spMap]
      have : ((TrivSqZeroExt.fstHom R R R).toRingHom).comp (algebraMap R (DualNumber R)) = RingHom.id R := by
        refine RingHom.ext fun a => ?_
        simp [TrivSqZeroExt.algebraMap_eq_inl]
      rw [this]
      show Spec.map (𝟙 _) ≫ x' = x'
      rw [Spec.map_id, Category.id_comp]

theorem exists_vec {G : Over (Sp R)} [GrpObj G] (σ : R →+* R') (w : epsR R ⟶ G) :
    ∃ U : epsAt (spMap σ) ⟶ G, U.left = spMap (dualMap σ) ≫ w.left ∧ (IsTangent w → IsTanAt G (spMap σ) U) := by
  have h1 : w.left ≫ G.hom = spMap (algebraMap R (DualNumber R)) := Over.w w
  refine ⟨Over.homMk (spMap (dualMap σ) ≫ w.left) (by
    show (spMap (dualMap σ) ≫ w.left) ≫ G.hom = spMap (algebraMap R' (DualNumber R')) ≫ spMap σ
    rw [Category.assoc, h1, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_alg]), rfl, fun ht => ?_⟩
  unfold IsTanAt
  rw [one_left]
  unfold IsTangent at ht
  show spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (dualMap σ) ≫ w.left = _
  rw [← Category.assoc, spMap_comp_spMap, fst_comp_dualMap, ← spMap_comp_spMap, Category.assoc, ht]
  rfl

theorem mono_alg (K : Type) [Field K] [NumberField K] : Mono (spMap (algebraMap (𝓞 K) K)) := by
  have : Epi (CommRingCat.ofHom (algebraMap (𝓞 K) K)) := IsLocalization.epi (nonZeroDivisors (𝓞 K)) K
  exact Scheme.Spec.map_mono (CommRingCat.ofHom _).op

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {Z : ∀ b : Bool, Curve0 H (sgnRt H b)} {c : Coeff l} {FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty} {i : Fin FU.n}
  {P : (FU.Di i).La →+ (Fin g → ℂ)} {hP : IsPeriod (FU.Di i) ty P}

abbrev sg (X : CMPack Z c FU i hP) (s : X.K →+* ℂ) : 𝓞 X.K →+* ℂ := s.comp (algebraMap (𝓞 X.K) X.K)

theorem exists_lift (X : CMPack Z c FU i hP) (b : Bool) (a : PureType.lat hP (sgnRt H b))
    (u : epsAt (under X.y) ⟶ Xo.univ.t.G) (hu : X.IsImage b a u) (s : X.K →+* ℂ)
    (Ux : epsAt (spMap (sg X s)) ⟶ X.B.t.G)
    (hUx : Ux.left = spMap (dualMap (sg X s)) ≫ (X.C b).v.left ≫ (X.ψ b a).left) :
    ∃ U' : epsAt (spMap s) ⟶ X.t.G, U'.left ≫ X.m.φ = spMap (dualMap s) ≫ u.left ∧ U'.left ≫ X.m'.φ = Ux.left := by
  obtain ⟨ρ, h1, h2⟩ := hu
  have hm := mono_alg X.K
  have hw : ρ ≫ X.t.G.hom = spMap (algebraMap X.K (DualNumber X.K)) := by
    rw [← cancel_mono (spMap (algebraMap (𝓞 X.K) X.K)), Category.assoc, ← X.m'.cart.1.w, ← Category.assoc, h2,
      Category.assoc, Category.assoc, Over.w (X.ψ b a)]
    have e1 : (X.C b).v.left ≫ (X.C b).P.A.hom = spMap (algebraMap (𝓞 X.K) (DualNumber (𝓞 X.K))) := Over.w (X.C b).v
    rw [e1, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_alg]
  refine ⟨Over.homMk (spMap (dualMap s) ≫ ρ) (by
    show (spMap (dualMap s) ≫ ρ) ≫ X.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap s
    rw [Category.assoc, hw, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_alg]), ?_, ?_⟩
  · show (spMap (dualMap s) ≫ ρ) ≫ X.m.φ = _
    rw [Category.assoc, h1]
  · show (spMap (dualMap s) ≫ ρ) ≫ X.m'.φ = _
    rw [Category.assoc, h2, hUx, ← Category.assoc, spMap_comp_spMap, dualMap_comp_dualMap]

theorem one_tangent (X : CMPack Z c FU i hP) (b : Bool) (a : PureType.lat hP (sgnRt H b)) :
    IsTangent ((X.C b).v ≫ X.ψ b a) := by
  have h1 : IsTangent (X.C b).v := (X.C b).basis.1 0
  have h2 : IsMonHom (X.ψ b a) := ((X.fam b).1 a).isMonHom
  unfold IsTangent at h1 ⊢
  rw [Over.comp_left, ← Category.assoc, h1, ← Over.comp_left, IsMonHom.one_hom]

theorem w_eq (X : CMPack Z c FU i hP) (b : Bool) (τ : E →+* ℂ) (hτ : τ (H.rt : E) = sgnRt H b) (s : X.K →+* ℂ) :
    s (X.β (tauE c τ (H.w0 : E))) = sg X s (X.ω b) := by
  show s _ = s _
  congr 1
  refine Subtype.ext ?_
  have e1 := (X.map b).1
  have e2 := (Z b).hω
  have e3 : 2 * τ (H.w0 : E) = 1 + τ (H.rt : E) := by
    have h0 : (2 : E) * (H.w0 : E) = 1 + (H.rt : E) := by
      have := congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
      simp only [map_mul, map_add, map_one, map_ofNat] at this
      exact this
    have := congrArg τ h0
    rwa [map_mul, map_add, map_one, map_ofNat] at this
  have e4 : (((X.ω b : 𝓞 X.K) : X.K) : ℂ) = (((Z b).ω : (Z b).M) : ℂ) := by rw [← e1]; rfl
  have e5 : ((X.β (tauE c τ (H.w0 : E)) : X.K) : ℂ) = τ (H.w0 : E) := rfl
  rw [e4, e5]
  rw [hτ, ← e2] at e3
  linear_combination (1/2 : ℂ) * e3

def kap (X : CMPack Z c FU i hP) (τ : E →+* ℂ) (s : X.K →+* ℂ) : OK H →+* ℂ :=
  (s.comp (X.β.comp (tauE c τ))).comp ((algebraMap (𝓞 E) E).comp (OK H).val.toRingHom)

theorem gram_family (X : CMPack Z c FU i hP) (b : Bool) (τ : E →+* ℂ) (hτ : τ (H.rt : E) = sgnRt H b) (s : X.K →+* ℂ)
    (r : ℝ) (hr : IsLieNormSq (Z b).C.P (Z b).C.v
      ((s.comp (IntermediateField.inclusion (X.hM b)).toRingHom).comp (algebraMap (𝓞 (Z b).M) (Z b).M)) r)
    {M : ℕ} (aq : Fin M → PureType.lat hP (sgnRt H b)) (Wq : Fin M → (epsAt (under X.y) ⟶ Xo.univ.t.G))
    (hW : ∀ q, X.IsImage b (aq q) (Wq q)) (V : Fin M → (epsAt (under (spMap s ≫ X.y)) ⟶ Xo.univ.t.G))
    (hV : ∀ q, (V q).left = spMap (dualMap s) ≫ (Wq q).left) :
    (∀ q, IsTanAt Xo.univ.t.G (under (spMap s ≫ X.y)) (V q)) ∧
    IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under (spMap s ≫ X.y)) V
      (Matrix.of fun q q' => r * kap X τ s (X.h b (aq q) (aq q'))) := by
  have hU := fun q => exists_vec (sg X s) ((X.C b).v ≫ X.ψ b (aq q))
  choose U hUl hUt using hU
  have hU' := fun q => exists_lift X b (aq q) (Wq q) (hW q) s (U q) (hUl q)
  choose U' h1 h2 using hU'
  have hnorm : IsLieNormSq (X.C b).P (X.C b).v (sg X s) r :=
    (T.lie_norm_sq_base_change E H _ _ _ _ (Z b).C (X.C b) _ (X.φ b) (sg X s) r (X.map b)).1 hr
  have hk : kap X τ s (wK H) = sg X s (X.ω b) := w_eq X b τ hτ s
  have g0 := T.lie_norm_square_of_family E H (FU.Di i) (𝓞 X.K) (X.ω b) (X.C b) X.B (fun x x' => X.h b x x') _ (X.ψ b) (sg X s)
    (kap X τ s) r M aq U (X.fam b) hk hnorm hUl
  have hx1 : spMap (sg X s) = spMap s ≫ spMap (algebraMap (𝓞 X.K) X.K) := (spMap_comp_spMap _ _).symm
  have hx2 : under (spMap s ≫ X.y) = spMap s ≫ under X.y := Category.assoc _ _ _
  have hV2 : ∀ q, (V q).left = (U' q).left ≫ X.m.φ := fun q => (hV q).trans (h1 q).symm
  have hU2 : ∀ q, (U q).left = (U' q).left ≫ X.m'.φ := fun q => (h2 q).symm
  have g1 := (T.hodge_gram_invariant_pullback E H _ _ X.B.t X.t _ X.m' (spMap s) (spMap (sg X s)) M U' U _ hx1 hU2).2 g0
  have g2 := (T.hodge_gram_invariant_pullback E H _ _ Xo.univ.t X.t _ X.m (spMap s) (under (spMap s ≫ X.y)) M U' V _ hx2 hV2).1 g1
  refine ⟨fun q => ?_, g2⟩
  exact (tan_iff X.m hx2 (U' q) (V q) (hV2 q)).1
    ((tan_iff X.m' hx1 (U' q) (U q) (hU2 q)).2 (hUt q (one_tangent X b (aq q))))

theorem mat_id {n M : ℕ} {I : Type} [Fintype I] [DecidableEq I] (e : Fin M ≃ Fin n × I) (x : I → ℂ)
    (G : Fin n × I → Fin n × I → ℂ) (A : Matrix (Fin n) (Fin M) ℂ)
    (hA : ∀ k q, A k q = if (e q).1 = k then x (e q).2 else 0) (k k' : Fin n) :
    (A * Matrix.of (fun q q' => G (e q) (e q')) * Aᴴ) k k' =
      ∑ m, ∑ m', x m * G (k, m) (k', m') * starRingEnd ℂ (x m') := by
  have hl : ∀ (k : Fin n) (F : Fin M → ℂ) (F' : Fin n × I → ℂ), (∀ q, F q = F' (e q)) →
      ∑ q, A k q * F q = ∑ m, x m * F' (k, m) := fun k F F' hF => by
    rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type, Finset.sum_eq_single k]
    · simp [hA, hF]
    · intro b _ hb
      simp [hA, hb]
    · simp
  have hr : ∀ (k : Fin n) (F : Fin M → ℂ) (F' : Fin n × I → ℂ), (∀ q, F q = F' (e q)) →
      ∑ q, F q * star (A k q) = ∑ m, F' (k, m) * starRingEnd ℂ (x m) := fun k F F' hF => by
    rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type, Finset.sum_eq_single k]
    · simp [hA, hF]
    · intro b _ hb
      simp [hA, hb]
    · simp
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  rw [hr k' _ (fun p' => ∑ m, x m * G (k, m) p') (fun q' => hl k _ (fun p => G p (e q')) fun q => rfl)]
  simp only [Finset.sum_mul]
  exact Finset.sum_comm

end GlobalTheory.CompanionTheory.Ar.Fl.GInf

namespace GlobalTheory.CompanionTheory.Ar.Fl.GInf

theorem hodgeGram_cmVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (b : Bool) (τ : E →+* ℂ) (n : ℕ) (a : Fin n → PureType.lat hP (sgnRt H b)) (v : Vecs X.y n) (s : X.K →+* ℂ) (y' : Sp ℂ ⟶ Xo.XF c) (v' : Vecs y' n) (r : ℝ), τ (H.rt : E) = sgnRt H b → (∀ k, X.IsCMVec b τ (a k) (v k)) → y' = spMap s ≫ X.y → (∀ k, (v' k).left = spMap (dualMap s) ≫ (v k).left) → IsLieNormSq (Z b).C.P (Z b).C.v ((s.comp (IntermediateField.inclusion (X.hM b)).toRingHom).comp (algebraMap (𝓞 (Z b).M) (Z b).M)) r → IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y') v' (Matrix.of fun k k' => r * ((X.ε b : ℤ) : ℂ) * s (X.β (tauE c τ ((H.rt : E) * sesq (FU.Di i) (a k) (a k'))))) := by
  intro E _ _ _ H D l Xo c g ty FU i Z P hP X b τ n a v s y' v' r hτ hv hy hv' hr
  classical
  subst hy
  have hx2 : under (spMap s ≫ X.y) = spMap s ≫ under X.y := Category.assoc _ _ _
  let e0 : Fin (Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E))) ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 E) :=
    (Fintype.equivFin _).symm
  let e : Fin (n * Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E))) ≃
      Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 E) :=
    finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) e0)
  choose nk ek uk h1 h2 using hv
  let W₂ : Fin n → Module.Free.ChooseBasisIndex ℤ (𝓞 E) → (epsAt (under X.y) ⟶ Xo.univ.t.G) :=
    fun k m => uk k ((ek k).symm m)
  have hW₂ : ∀ k m, X.IsImage b (RingOfIntegers.basis E m • a k) (W₂ k m) := fun k m => by
    have := h1 k ((ek k).symm m)
    rwa [Equiv.apply_symm_apply] at this
  have hVex := fun q => exists_bc (G := Xo.univ.t.G) s (under X.y) hx2 (W₂ (e q).1 (e q).2)
  choose V hV using hVex
  obtain ⟨ht, hg⟩ := gram_family X b τ hτ s r hr (fun q => RingOfIntegers.basis E (e q).2 • a (e q).1)
    (fun q => W₂ (e q).1 (e q).2) (fun q => hW₂ _ _) V hV
  let x : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℂ := fun m => s (X.β (tauE c τ (HT.dualInt E m)))
  let A : Matrix (Fin n) (Fin (n * Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)))) ℂ :=
    Matrix.of fun k q => if (e q).1 = k then x (e q).2 else 0
  have hcomb : ∀ k, Fl.IsComb (A k) V (v' k) := fun k => by
    have b1 := isComb_bc s (under X.y) hx2 _ (uk k) (v k) (fun j => V (e.symm (k, ek k j))) (v' k)
      (fun j => by
        rw [hV]
        simp only [Equiv.apply_symm_apply, W₂, Equiv.symm_apply_apply]) (hv' k) (h2 k)
    refine isComb_pad (A k) V (fun j => e.symm (k, ek k j)) (fun j j' hj => ?_) (fun j => ?_) (fun _ => rfl)
      (fun q hq => ?_) ht b1
    · have := e.symm.injective hj
      exact (ek k).injective (Prod.ext_iff.1 this).2
    · simp [A, x]
    · by_contra hne
      have hk : (e q).1 = k := by
        by_contra hk
        exact hne (by simp [A, hk])
      refine hq ⟨(ek k).symm (e q).2, ?_⟩
      simp only [Equiv.apply_symm_apply]
      rw [← hk]
      exact e.symm_apply_apply q
  have g3 := T.hodge_gram_linear_combination _ _ _ _ _ _ V v' _ A ht hg hcomb
  convert g3 using 1
  ext k k'
  have m1 := mat_id e x (fun p p' => (r : ℂ) * kap X τ s (X.h b
    ((RingOfIntegers.basis E p.2 • a p.1 : PureType.lat hP (sgnRt H b)) : (FU.Di i).La)
    ((RingOfIntegers.basis E p'.2 • a p'.1 : PureType.lat hP (sgnRt H b)) : (FU.Di i).La))) A (fun _ _ => rfl) k k'
  have m2 := T.dual_basis_hermitian_sum E H (FU.Di i) (X.ε b) (X.h b) (s.comp (X.β.comp (tauE c τ))) (kap X τ s) _ e0 (a k) (a k')
    (X.kform b) rfl
  dsimp only at m1
  have m3 : ∑ m, ∑ m', x m * kap X τ s (X.h b (RingOfIntegers.basis E m • (a k : (FU.Di i).La))
      (RingOfIntegers.basis E m' • (a k' : (FU.Di i).La))) * starRingEnd ℂ (x m') =
      ((X.ε b : ℤ) : ℂ) * s (X.β (tauE c τ ((H.rt : E) * sesq (FU.Di i) (a k) (a k')))) := by
    refine Eq.trans ?_ m2
    rw [← Equiv.sum_comp e0]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Equiv.sum_comp e0]
    rfl
  refine Eq.trans ?_ m1.symm
  rw [Matrix.of_apply, _root_.mul_assoc, ← m3, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m' _ => ?_
  show (r : ℂ) * (x m * kap X τ s (X.h b (RingOfIntegers.basis E m • (a k : (FU.Di i).La))
      (RingOfIntegers.basis E m' • (a k' : (FU.Di i).La))) * starRingEnd ℂ (x m')) =
    x m * ((r : ℂ) * kap X τ s (X.h b (RingOfIntegers.basis E m • (a k : (FU.Di i).La))
      (RingOfIntegers.basis E m' • (a k' : (FU.Di i).La)))) * starRingEnd ℂ (x m')
  ring

end GlobalTheory.CompanionTheory.Ar.Fl.GInf
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_pack_period_product : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (b : Bool) (τ : E →+* ℂ) (n : ℕ) (a : Fin n → PureType.lat hP (sgnRt H b)) (v : Vecs X.y n) (s : X.K →+* ℂ) (y' : Sp ℂ ⟶ Xo.XF c) (v' : Vecs y' n) (r : ℝ), τ (H.rt : E) = sgnRt H b → (∀ k, X.IsCMVec b τ (a k) (v k)) → y' = spMap s ≫ X.y → (∀ k, (v' k).left = spMap (dualMap s) ≫ (v k).left) → IsLieNormSq (Z b).C.P (Z b).C.v ((s.comp (IntermediateField.inclusion (X.hM b)).toRingHom).comp (algebraMap (𝓞 (Z b).M) (Z b).M)) r → IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y') v' (Matrix.of fun k k' => r * ((X.ε b : ℤ) : ℂ) * s (X.β (tauE c τ ((H.rt : E) * sesq (FU.Di i) (a k) (a k'))))) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Fl.GInf.hodgeGram_cmVec
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.InfPlace

theorem log_norm_det_scaled {E : Type} [Field E] (σ : E →+* ℂ) (rt : E) (d : ℕ) (hd : 0 < d)
    (hrt : rt ^ 2 = -(d : E)) (r : ℝ) (hr : 0 < r) (ε : ℤˣ) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) E) (hM : M.det ≠ 0) (Γ : Matrix (Fin n) (Fin n) ℂ)
    (hΓ : ∀ k k', Γ k k' = (r : ℂ) * ((ε : ℤ) : ℂ) * σ (rt * M k k')) :
    Real.log ‖Γ.det‖ = (n : ℝ) * (Real.log r + Real.log d / 2) + Real.log ‖σ M.det‖ := by
  have hΓ' : Γ = ((r : ℂ) * ((ε : ℤ) : ℂ) * σ rt) • (σ.mapMatrix M) := by
    ext k k'
    simp only [hΓ, Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, smul_eq_mul, map_mul]
    ring
  have hdet : Γ.det = ((r : ℂ) * ((ε : ℤ) : ℂ) * σ rt) ^ n * σ M.det := by
    rw [hΓ', Matrix.det_smul, Fintype.card_fin, RingHom.map_det]
  have hε : ‖((ε : ℤ) : ℂ)‖ = 1 := by
    rcases Int.units_eq_one_or ε with h | h <;> simp [h]
  have hs : ‖σ rt‖ ^ 2 = d := by
    have h1 : σ rt ^ 2 = -(d : ℂ) := by
      rw [← map_pow, hrt]
      simp
    have h2 := congrArg norm h1
    simpa [norm_pow] using h2
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hs0 : ‖σ rt‖ ≠ 0 := by
    intro h
    rw [h] at hs
    have h0 : (d : ℝ) = 0 := by simpa using hs.symm
    linarith
  have hlog : Real.log ‖σ rt‖ = Real.log d / 2 := by
    have h3 := congrArg Real.log hs
    rw [Real.log_pow] at h3
    push_cast at h3
    linarith
  have hσM : σ M.det ≠ 0 := (map_ne_zero σ).2 hM
  have hpos : ‖((r : ℂ) * ((ε : ℤ) : ℂ) * σ rt) ^ n‖ ≠ 0 := by
    rw [norm_pow, norm_mul, norm_mul, hε, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, _root_.mul_one]
    exact pow_ne_zero _ (mul_ne_zero hr.ne' hs0)
  rw [hdet, norm_mul, Real.log_mul hpos (norm_ne_zero_iff.2 hσM), norm_pow, norm_mul, norm_mul, hε,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, _root_.mul_one, Real.log_pow,
    Real.log_mul hr.ne' hs0, hlog]

theorem conj_eq_neg_of_sq {d : ℕ} (hd : 0 < d) {z : ℂ} (hz : z ^ 2 = -(d : ℂ)) :
    starRingEnd ℂ z = -z :=
  _root_.UpperTheory.Reformulated.B.ConjEqNegOfSqEqNegNat₂.main hd hz

theorem hasInfNorm_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ) (k : IntermediateField ℚ ℂ) [NumberField k] (hc : c.F ≤ k) (hM : ∀ b, (Z b).M ≤ k) (r : k) (s : k →+* ℂ) (n n' t : ℝ), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → (∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P → y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U) → IsLineFn U τ φ → LinearIndependent (𝓞 E) e → IsConstMul U τ φ FU i e ρ → r ≠ 0 → (r : ℂ) * (Z true).z ^ D.p = ρ * (Z false).z ^ D.q → 0 < n → 0 < n' → IsLieNormSq (Z true).C.P (Z true).C.v ((s.comp (IntermediateField.inclusion (hM true)).toRingHom).comp (algebraMap (𝓞 (Z true).M) (Z true).M)) n → IsLieNormSq (Z false).C.P (Z false).C.v ((s.comp (IntermediateField.inclusion (hM false)).toRingHom).comp (algebraMap (𝓞 (Z false).M) (Z false).M)) n' → HasInfNorm U τ φ (s.comp (IntermediateField.inclusion hc).toRingHom) t → t = Real.log ‖s r‖ + ((D.p : ℝ) / 2 * (Real.log n + Real.log H.d / 2) - (D.q : ℝ) / 2 * (Real.log n' + Real.log H.d / 2)) + Real.log ‖s ((((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) (gramE (FU.Di i) e).det)‖ / 2 := by
  intro E _ _ _ H D l Xo c g ty FU i Z U τ φ e ρ k _ hc hM r s n n' t hty hτ hU hline he hconst hr hrz hn hn' hLt hLf hinf
  classical
  obtain ⟨P, hP, x, hx, X, v, w, hkK, hloc, hfr⟩ :=
    GlobalTheory.T.exists_cm_period_embedding E H D l Xo c g ty FU i Z τ ⟨2, Nat.prime_two⟩ k inferInstance hty hτ
  have hxli : LinearIndependent (𝓞 E) x := hloc.1
  have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
    simp [(FU.sig i).1, (FU.sig i).2]
  obtain ⟨T, hT, hgram, hTdet, -⟩ := GlobalTheory.T.exists_transition_matrix_gram E H (FU.Di i) _ x e hcard he
  have hTne := hTdet hxli
  have hGe := (GlobalTheory.T.gram_det_ne_zero_local_basis_cofinite E H (FU.Di i) _ e hcard he).1
  obtain ⟨hfram, hval⟩ := GlobalTheory.T.cm_pack_pure_frame_open E H D l Xo c g ty FU i Z P hP X x hx U τ φ e ρ T v w hty hτ hU hline he
    hconst hxli hT hfr
  obtain ⟨s', hs'⟩ := GlobalTheory.T.exists_extension_embedding_alg_closed k X.K ℂ (IntermediateField.inclusion hkK).toRingHom s
  have hs'a : ∀ a : k, s' (IntermediateField.inclusion hkK a) = s a := fun a => DFunLike.congr_fun hs' a
  have hβ : s'.comp X.β = s.comp (IntermediateField.inclusion hc).toRingHom := by
    ext a
    exact hs'a (IntermediateField.inclusion hc a)
  have hMs : ∀ b, s'.comp (IntermediateField.inclusion (X.hM b)).toRingHom =
      s.comp (IntermediateField.inclusion (hM b)).toRingHom := by
    intro b
    ext a
    exact hs'a (IntermediateField.inclusion (hM b) a)

  let y' : Sp ℂ ⟶ Xo.XF c := spMap s' ≫ X.y
  have hy' : under y' = spMap s' ≫ under X.y := Category.assoc _ _ _
  obtain ⟨⟨v', hv'⟩, hvI⟩ := GlobalTheory.T.tangent_vectors_base_change E H Xo.X Xo.univ.t X.K ℂ s' (under X.y) (under y')
    (X.β.comp (tauIn c τ)) D.p v hy'
  obtain ⟨⟨w', hw'⟩, hwI⟩ := GlobalTheory.T.tangent_vectors_base_change E H Xo.X Xo.univ.t X.K ℂ s' (under X.y) (under y')
    (X.β.comp (tauIn c (ComplexEmbedding.conjugate τ))) D.q w hy'
  have hfram' : IsFramed U τ (s.comp (IntermediateField.inclusion hc).toRingHom) y' v' w' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hβ]
      simp only [y', Category.assoc, hfram.1]
      simp [spMap, ← Spec.map_comp, CommRingCat.ofHom_comp]
    · rintro _ ⟨u, rfl⟩
      apply hfram.2.1
      exact ⟨(spMap s') u, by simp [y']⟩
    · rw [← hβ, RingHom.comp_assoc]
      exact (hvI v' hv').1 hfram.2.2.1
    · rw [← hβ, RingHom.comp_assoc]
      exact (hwI w' hw').1 hfram.2.2.2
  have hconjτ : ComplexEmbedding.conjugate τ (H.rt : E) = sgnRt H false := by
    simp only [sgnRt, ComplexEmbedding.conjugate_coe_eq, hτ]
    exact conj_eq_neg_of_sq H.d_prime.pos H.sqrt_neg_disc_sq
  have hΓ := GlobalTheory.T.cm_pack_period_product E H D l Xo c g ty FU i Z P hP X true τ D.p (fun a => ⟨x (.inl a), hx.1 a⟩) v s' y' v' n
    (by simpa [sgnRt] using hτ) hfr.1 rfl hv' (by rw [hMs]; exact hLt)
  have hΔ := GlobalTheory.T.cm_pack_period_product E H D l Xo c g ty FU i Z P hP X false (ComplexEmbedding.conjugate τ) D.q
    (fun a => ⟨x (.inr a), hx.2 a⟩) w s' y' w' n' hconjτ hfr.2 rfl hw' (by rw [hMs]; exact hLf)
  have hmain := hinf y' v' w' _ _ hfram' hΓ hΔ
  rw [hline.nat X.K ℂ s' X.β X.y v w y' v' w' hfram rfl hv' hw'] at hmain

  have hblock : gramE (FU.Di i) x =
      Matrix.fromBlocks (gramE (FU.Di i) (x ∘ Sum.inl)) 0 0 (gramE (FU.Di i) (x ∘ Sum.inr)) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b
    · rfl
    · exact (GlobalTheory.T.pure_type_lattices_orthogonal E H (FU.Di i) g ty P hP _ _ (hx.1 a) (hx.2 b)).1
    · exact (GlobalTheory.T.pure_type_lattices_orthogonal E H (FU.Di i) g ty P hP _ _ (hx.1 b) (hx.2 a)).2
    · rfl
  have hdet1 : (gramE (FU.Di i) x).det =
      (gramE (FU.Di i) (x ∘ Sum.inl)).det * (gramE (FU.Di i) (x ∘ Sum.inr)).det := by
    rw [hblock, Matrix.det_fromBlocks_zero₁₂]
  have hdet2 : (gramE (FU.Di i) x).det =
      T.det * (gramE (FU.Di i) e).det * IsCMField.complexConj E T.det := by
    have hc' : (T.map (IsCMField.complexConj E)).det = IsCMField.complexConj E T.det :=
      (RingHom.map_det (IsCMField.complexConj E : E →+* E) T).symm
    rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hc']
  have hconjne : IsCMField.complexConj E T.det ≠ 0 := by
    simpa using hTne
  have hG : (gramE (FU.Di i) (x ∘ Sum.inl)).det * (gramE (FU.Di i) (x ∘ Sum.inr)).det ≠ 0 := by
    rw [← hdet1, hdet2]
    exact mul_ne_zero (mul_ne_zero hTne hGe) hconjne
  have hG1 := left_ne_zero_of_mul hG
  have hG2 := right_ne_zero_of_mul hG

  let σ : E →+* ℂ := s'.comp (X.β.comp (tauE c τ))
  let σ' : E →+* ℂ := s'.comp (X.β.comp (tauE c (ComplexEmbedding.conjugate τ)))
  have hσ' : ∀ a, ‖σ' a‖ = ‖σ a‖ := by
    intro a
    have h1 : tauE c (ComplexEmbedding.conjugate τ) a = tauE c τ (IsCMField.complexConj E a) := by
      apply Subtype.ext
      change ComplexEmbedding.conjugate τ a = τ (IsCMField.complexConj E a)
      rw [IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]
    have h2 : σ' a = σ (IsCMField.complexConj E a) := by
      simp only [σ', σ, RingHom.comp_apply, h1]
    rw [h2, IsCMField.complexEmbedding_complexConj, RCLike.norm_conj]
  have hrt : ((H.rt : 𝓞 E) : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have hlΓ := log_norm_det_scaled σ (H.rt : E) H.d H.d_prime.pos hrt n hn (X.ε true)
    (gramE (FU.Di i) (x ∘ Sum.inl)) hG1
    (Matrix.of fun a a' => (n : ℂ) * ((X.ε true : ℤ) : ℂ) *
      s' (X.β (tauE c τ ((H.rt : E) * sesq (FU.Di i) (x (.inl a)) (x (.inl a')))))) (fun _ _ => rfl)
  have hlΔ := log_norm_det_scaled σ' (H.rt : E) H.d H.d_prime.pos hrt n' hn' (X.ε false)
    (gramE (FU.Di i) (x ∘ Sum.inr)) hG2
    (Matrix.of fun a a' => (n' : ℂ) * ((X.ε false : ℤ) : ℂ) *
      s' (X.β (tauE c (ComplexEmbedding.conjugate τ) ((H.rt : E) * sesq (FU.Di i) (x (.inr a)) (x (.inr a')))))) (fun _ _ => rfl)
  rw [hσ'] at hlΔ

  have hz := GlobalTheory.T.curve_z_ne_zero E H _ (Z true)
  have hval2 : ((φ X.K X.y v w : X.K) : ℂ) * τ T.det = (r : ℂ) * τ (gramE (FU.Di i) (x ∘ Sum.inr)).det := by
    apply mul_right_cancel₀ (pow_ne_zero D.p hz)
    rw [hval, ← hrz]
    ring
  have hK : (φ X.K X.y v w) * X.β (tauE c τ T.det) =
      IntermediateField.inclusion hkK r * X.β (tauE c τ (gramE (FU.Di i) (x ∘ Sum.inr)).det) :=
    Subtype.ext hval2
  have hS : s' (φ X.K X.y v w) * σ T.det = s r * σ (gramE (FU.Di i) (x ∘ Sum.inr)).det := by
    have := congrArg s' hK
    rw [map_mul, map_mul, hs'a] at this
    exact this
  have hφ0 : s' (φ X.K X.y v w) ≠ 0 := (map_ne_zero s').2 (hline.ne X.K X.β X.y v w hfram)
  have hσT : σ T.det ≠ 0 := (map_ne_zero σ).2 hTne
  have hσG2 : σ (gramE (FU.Di i) (x ∘ Sum.inr)).det ≠ 0 := (map_ne_zero σ).2 hG2
  have hσG1 : σ (gramE (FU.Di i) (x ∘ Sum.inl)).det ≠ 0 := (map_ne_zero σ).2 hG1
  have hσGe : σ (gramE (FU.Di i) e).det ≠ 0 := (map_ne_zero σ).2 hGe
  have hsr : s r ≠ 0 := (map_ne_zero s).2 hr
  have hl1 : Real.log ‖s' (φ X.K X.y v w)‖ + Real.log ‖σ T.det‖ =
      Real.log ‖s r‖ + Real.log ‖σ (gramE (FU.Di i) (x ∘ Sum.inr)).det‖ := by
    rw [← Real.log_mul (norm_ne_zero_iff.2 hφ0) (norm_ne_zero_iff.2 hσT),
      ← Real.log_mul (norm_ne_zero_iff.2 hsr) (norm_ne_zero_iff.2 hσG2), ← norm_mul, ← norm_mul, hS]
  have hl2 : Real.log ‖σ (gramE (FU.Di i) (x ∘ Sum.inl)).det‖ + Real.log ‖σ (gramE (FU.Di i) (x ∘ Sum.inr)).det‖ =
      2 * Real.log ‖σ T.det‖ + Real.log ‖σ (gramE (FU.Di i) e).det‖ := by
    have h1 := congrArg σ (hdet1.symm.trans hdet2)
    rw [map_mul, map_mul, map_mul, IsCMField.complexEmbedding_complexConj] at h1
    have h2 := congrArg norm h1
    rw [norm_mul, norm_mul, norm_mul, RCLike.norm_conj] at h2
    have h3 := congrArg Real.log h2
    rw [Real.log_mul (norm_ne_zero_iff.2 hσG1) (norm_ne_zero_iff.2 hσG2),
      Real.log_mul (mul_ne_zero (norm_ne_zero_iff.2 hσT) (norm_ne_zero_iff.2 hσGe)) (norm_ne_zero_iff.2 hσT),
      Real.log_mul (norm_ne_zero_iff.2 hσT) (norm_ne_zero_iff.2 hσGe)] at h3
    linarith
  have hlast : s ((((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) (gramE (FU.Di i) e).det) =
      σ (gramE (FU.Di i) e).det :=
    (DFunLike.congr_fun hβ (tauE c τ (gramE (FU.Di i) e).det)).symm
  rw [hlast]
  rw [hlΓ, hlΔ] at hmain
  linarith

end GlobalTheory.CompanionTheory.Ar.Fl.InfPlace
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_function_cm_number_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ) (k : IntermediateField ℚ ℂ) [NumberField k] (hc : c.F ≤ k) (hM : ∀ b, (Z b).M ≤ k) (r : k) (s : k →+* ℂ) (n n' t : ℝ), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → (∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P → y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U) → IsLineFn U τ φ → LinearIndependent (𝓞 E) e → IsConstMul U τ φ FU i e ρ → r ≠ 0 → (r : ℂ) * (Z true).z ^ D.p = ρ * (Z false).z ^ D.q → 0 < n → 0 < n' → IsLieNormSq (Z true).C.P (Z true).C.v ((s.comp (IntermediateField.inclusion (hM true)).toRingHom).comp (algebraMap (𝓞 (Z true).M) (Z true).M)) n → IsLieNormSq (Z false).C.P (Z false).C.v ((s.comp (IntermediateField.inclusion (hM false)).toRingHom).comp (algebraMap (𝓞 (Z false).M) (Z false).M)) n' → HasInfNorm U τ φ (s.comp (IntermediateField.inclusion hc).toRingHom) t → t = Real.log ‖s r‖ + ((D.p : ℝ) / 2 * (Real.log n + Real.log H.d / 2) - (D.q : ℝ) / 2 * (Real.log n' + Real.log H.d / 2)) + Real.log ‖s ((((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) (gramE (FU.Di i) e).det)‖ / 2 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Fl.InfPlace.hasInfNorm_value
end

section
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM

theorem flatDegree_mean_ext {M k : Type} [Field M] [NumberField M] [Field k] [NumberField k] (f : M →+* k)
    (F : (M →+* ℂ) → ℝ) :
    (∑ s : k →+* ℂ, F (s.comp f)) / Module.finrank ℚ k = (∑ s, F s) / Module.finrank ℚ M := by
  have h := GlobalTheory.T.sum_embeddings_base_change M k ℂ f F
  have hM : (Module.finrank ℚ M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hk : (Module.finrank ℚ k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  rw [div_eq_div_iff hk hM]
  linear_combination h

theorem flatDegree_sum_conj {E A : Type} [Field E] [NumberField E] [IsCMField E] [Field A] [CharZero A]
    (F : A → ℝ) (t : E) :
    ∑ j : E →+* A, F (j (IsCMField.complexConj E t)) = ∑ j : E →+* A, F (j t) := by
  let c : E →+* E := RingHomClass.toRingHom (IsCMField.complexConj E)
  let σ : (E →+* A) ≃ (E →+* A) :=
    { toFun := fun j => j.comp c
      invFun := fun j => j.comp c
      left_inv := fun j => RingHom.ext fun x => congrArg j (IsCMField.complexConj_apply_apply E x)
      right_inv := fun j => RingHom.ext fun x => congrArg j (IsCMField.complexConj_apply_apply E x) }
  exact Equiv.sum_comp σ (fun j => F (j t))

theorem flatDegree_logOm_re (E : Type) [Field E] [NumberField E] {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) {x : ℝ}
    (hx : (x : ℂ) = (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √d) : ℝ) -
      deriv χ.LFunction 1 / χ.LFunction 1) :
    (logOm E χ).re = x - Real.log (rootDiscr E) + Real.log (Real.sqrt d) := by
  have hrd : 0 < rootDiscr E := by
    unfold NumberField.rootDiscr
    apply Real.rpow_pos_of_pos
    exact_mod_cast abs_pos.mpr (NumberField.discr_ne_zero E)
  have hd : 0 < √(d : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d))
  have hL : deriv χ.LFunction 1 / χ.LFunction 1 =
      ((Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √d) : ℝ) : ℂ) - x := by
    rw [hx]; ring
  unfold GlobalTheory.CM.logOm
  rw [hL]
  simp only [Complex.sub_re, Complex.ofReal_re]
  rw [Real.log_div (by positivity) hrd.ne', Real.log_div (by positivity) hd.ne']
  ring

theorem flatDegree : FlatDegree := by
  unfold FlatDegree
  intro E _ _ _ H D l Xo c g ty FU i U τ φ _ N _ χ hχ hty hrt hflat hN
  obtain ⟨mem, line, ⟨e, ρ, hli, hcm⟩⟩ := hflat
  obtain ⟨hNinf, hNfin⟩ := hN
  have hsq : ∀ b : Bool, sgnRt H b ^ 2 = -(H.d : ℂ) := by
    intro b
    cases b <;> simp [sgnRt, neg_sq, H.sqrt_neg_disc_sq]
  choose Z x hz hper hxv using fun b => GlobalTheory.T.chowla_selberg_period E H χ hχ (sgnRt H b) (hsq b)
  have hx : x false = x true := Complex.ofReal_injective ((hxv false).trans (hxv true).symm)
  haveI := (Z true).nf
  haveI := (Z false).nf
  obtain ⟨n₁, hn₁, hm₁⟩ := hper true
  obtain ⟨n₀, hn₀, hm₀⟩ := hper false
  obtain ⟨k, hkfd, r, hc, hM, hr0, hrz⟩ :=
    GlobalTheory.T.frame_function_cm_value E H D l Xo c g ty FU i Z U τ φ e ρ hty hrt mem line hli hcm
  haveI := hkfd
  haveI : NumberField k := ⟨⟩
  choose t ht1 ht2 ht3 using fun ℓ : Nat.Primes =>
    GlobalTheory.T.frame_function_cm_height E H D l Xo c g ty FU i Z U τ φ e ρ k hc hM r ℓ hty hrt mem line hli hcm hr0 hrz
  have hgram := GlobalTheory.T.gram_det_ne_zero_local_basis_cofinite E H (FU.Di i) (Fin D.p ⊕ Fin D.q) e
    (by rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, (FU.sig i).1, (FU.sig i).2]) hli
  have hrt2 : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have h := congrArg (algebraMap (NumberField.RingOfIntegers E) E) H.rt_sq
    rw [map_pow, map_neg, map_natCast] at h
    exact h
  have hmean₁ := flatDegree_mean_ext (IntermediateField.inclusion (hM true)).toRingHom
    (fun σ => Real.log (n₁ σ))
  have hmean₀ := flatDegree_mean_ext (IntermediateField.inclusion (hM false)).toRingHom
    (fun σ => Real.log (n₀ σ))
  have hfinite : {ℓ : Nat.Primes | ∃ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖ ≠ 0}.Finite := by
    apply hgram.2.subset
    intro ℓ hℓ hloc
    obtain ⟨j, hj⟩ := hℓ
    exact hj (ht2 ℓ hloc j)
  have key := GlobalTheory.T.hermitian_metric_log_norm_formula (↥k) E (RingHom.comp (IntermediateField.inclusion hc : ↥c.F →+* ↥k) (GlobalTheory.CompanionTheory.Ar.Fl.tauE c τ))
    (N.ext (IntermediateField.inclusion hc).toRingHom) r (GlobalTheory.CompanionTheory.Ar.Fl.gramE (FU.Di i) e).det
    (H.rt : E) D.p D.q H.d
    (fun s => n₁ (s.comp (IntermediateField.inclusion (hM true)).toRingHom))
    (fun s => n₀ (s.comp (IntermediateField.inclusion (hM false)).toRingHom))
    (x true) t (fun ℓ => IsCMField.complexConj E (t ℓ))
    hr0 hgram.1 (Nat.Prime.pos H.d_prime) hrt2
    (by rw [neg_div, hmean₁, ← hm₁]; rfl)
    (by rw [neg_div, hmean₀, ← hx, ← hm₀]; rfl)
    (fun s => GlobalTheory.T.frame_function_cm_number_field E H D l Xo c g ty FU i Z U τ φ e ρ k hc hM r s
      (n₁ (s.comp (IntermediateField.inclusion (hM true)).toRingHom))
      (n₀ (s.comp (IntermediateField.inclusion (hM false)).toRingHom))
      (N.inf (s.comp (IntermediateField.inclusion hc).toRingHom))
      hty hrt mem line hli hcm hr0 hrz
      (hn₁ _).1 (hn₀ _).1 (((hn₁ _).2 _).mpr rfl) (((hn₀ _).2 _).mpr rfl)
      (hNinf _))
    (fun ℓ => flatDegree_sum_conj (fun z : ℂ_[ℓ] => Real.log ‖z‖) (t ℓ))
    (fun ℓ j => ht1 ℓ j) hfinite
    (fun ℓ j => ht3 ℓ j _ (hNfin ℓ (j.comp (IntermediateField.inclusion hc).toRingHom)))
  obtain ⟨hAd, hdeg⟩ := key
  obtain ⟨hdeg', hAd'⟩ := GlobalTheory.CompanionTheory.Ar.Fl.logNorms_ext_deg_isAdelic (↥c.F) (↥k)
    (IntermediateField.inclusion hc).toRingHom N
  refine ⟨hAd'.mp hAd, ?_⟩
  rw [← hdeg', hdeg, flatDegree_logOm_re E χ (hxv true)]

end GlobalTheory.CompanionTheory.Ar.Fl
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.FlatDegree_holds : GlobalTheory.CompanionTheory.Ar.Fl.FlatDegree := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Fl.flatDegree
end
