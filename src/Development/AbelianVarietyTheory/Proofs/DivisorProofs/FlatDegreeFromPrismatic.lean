import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanExistenceEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmDifferentFromIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealFromPlaceShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHTFrameCpAndNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmGoodReductionPointOnComponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineDegreeEqEigenLatticeDegreeSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateConstantEverywhere
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.PlaceShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMapToModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExOfFlatWtSome
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateInclusionRaynaudExtensionAlgebraicPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentEvLieOfLieTie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlCSurjectiveAndLinearIndependentBLie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieTieOfFrMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFinrankOfCokernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateKernelAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceShiftStOfPublished

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_existence_everywhere : Always fun U x => ArchEx U x := by
  first | exact @GlobalTheory.FlatCore.archEx_always | exact GlobalTheory.FlatCore.archEx_always | (intros; apply GlobalTheory.FlatCore.archEx_always <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.FlatCore

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem flatDegree_of_steps : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ logOm : ℝ, ArchEx U x → FinConst U x → FrameDeg U x logOm → FlatDegree U x logOm := by
  intro E _ _ _ H Dw l Xo c r U x hL logOm hA hF hD Z τ
  refine ⟨?_, fun s => ?_⟩
  · obtain ⟨s⟩ := hA Z τ
    choose ρ hρ using hF Z τ s
    have hP := GlobalTheory.FlatLine.hasPts U hL.pos hL.good hL.unf Z
    have hfin := (hD Z τ s ρ hρ).1
    refine ⟨⟨s.sig, s.inv, s.sig_mem, s.inv_mem, s.idem_sig, s.idem_inv, s.mul_inv, s.cInf, s.cInf_pos, s.norm_inf,
      ρ - flDefect_vw Dw c τ, fun w => image_eq_singleton_iff.2 ⟨hP.2 w, fun v hv => ?_⟩,
      (hfin.union (finite_flDefect_vw τ)).subset (Function.support_sub _ _)⟩⟩
    rw [hρ w v hv, Pi.sub_apply, add_sub_cancel]
  · have h := (hD Z τ (ArchSec.ofConst s.toFrame) s.toFrame.rho_vw fun w v hv => by
      have h1 := s.toFrame.val_eq hv
      rw [Pi.zero_apply, zero_add] at h1
      exact h1).2
    rw [s.deg_eq_toFrame, neg_neg, flatDegVal, ← h]
    rfl

end GlobalTheory.FlatCore

end
end

section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_different_from_ideal : IdealSt → GlobalTheory.FlatCore.CMDiffSt := by
  first | exact @GlobalTheory.FlatCore.CMDiff.cmDiffSt_of_idealSt | exact GlobalTheory.FlatCore.CMDiff.cmDiffSt_of_idealSt | (intros; apply GlobalTheory.FlatCore.CMDiff.cmDiffSt_of_idealSt <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCore.Fin

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem htValAt_nonempty (la : HeightOneSpectrum (𝓞 c.F)) {T : CDVR} {io : c.F →+* T.Fr} (y₀ : IntFr Xo c T io)
    (hy : y₀.IsAlg) : (htValAt la y₀).Nonempty := by
  obtain ⟨p, hp, ha, k, y, h⟩ := (GlobalTheory.CompHt.exists_isHTFrameCp_and_nonempty E H Dw l Xo c).1 T io y₀ hy
  exact ⟨_, p, hp, ha, k, y, h, rfl⟩

theorem finConst_of {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} (h₁ : HTConst U x) (h₂ : HTShift Xo c) :
    FinConst U x := fun Z τ s la => by
  obtain ⟨ρ, hρ⟩ := h₁ Z τ s la
  obtain ⟨κ, hκ⟩ := h₂ τ la
  refine ⟨ρ - κ, ?_⟩
  rintro _ ⟨⟨q, T, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩
  obtain ⟨w, hw⟩ := htValAt_nonempty la y hy.1
  have h3 := (hρ w ⟨T, io, e, y, ho, hy, hw⟩).symm.trans (hκ T io e y ho hy.1 w hw _ s.sig_mem)
  show nval T.V e (evI y s.sig) = _
  by_cases h0 : evI y s.sig = 0
  · rw [h0, nval_zero, EReal.top_add_coe] at h3
    exact absurd h3 (EReal.coe_ne_top ρ)
  · rw [nval_of_ne h0] at h3 ⊢
    rw [← EReal.coe_add, EReal.coe_eq_coe_iff] at h3
    rw [EReal.coe_eq_coe_iff, h3]; ring

theorem finConst_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ),
    Laws U x → HTShift Xo c → HTConst U x → FinConst U x :=
  by
  intro E _ _ _ H Dw l Xo c r U x _ h₂ h₁
  exact finConst_of h₁ h₂

end GlobalTheory.FlatCore.Fin

end
end

section
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.FlatCore

theorem frameDeg_of_cmDiff : CMDiffSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → FrameDeg U x (GlobalTheory.CM.logOm E χ).re := by
  intro hCM E _ _ _ H hH _ χ hχ Dw l Xo c r U x hL Z τ s ρ hρ
  obtain ⟨K, iF, iN, iA, y, ρ₀, σ₁, X, t₀, hy, hm₁, hm₂, hρ₀⟩ := GlobalTheory.T.exists_cm_goodReduction_point_on_component E H Dw l Xo c r U x hL Z
  obtain ⟨F⟩ := GlobalTheory.CM.GenFib.nonempty_of_baseChange GlobalTheory.polBaseChange_holds K X.B.pol
  obtain ⟨⟨h, hh⟩, -⟩ :=
    GlobalTheory.CM.LieMetric.exists_unique_isHerm GlobalTheory.thetaUnifAV_all GlobalTheory.abelianSchemeLaws_all.1 K X.B.pol F
  let f : 𝓞 E →+* K := (algebraMap c.F K).comp (embK c τ.1)
  have hf : ∀ a, IsIntegral ℤ (f a) := fun a =>
    (Algebra.IsIntegral.isIntegral (R := ℤ) a).map f.toIntAlgHom
  let t : 𝓞 E →+* 𝓞 K := f.codRestrict (integralClosure ℤ K).toSubring hf
  have ht : ∀ a, ((t a : 𝓞 K) : K) = algebraMap c.F K (embK c τ.1 a) := fun a => rfl
  obtain ⟨hfin, hdeg⟩ := GlobalTheory.T.flatLineDegree_eq_eigenLattice_degree_sub E H Dw l Xo c r U x hL Z τ s ρ hρ K y hy X.B t₀ hm₁ hm₂ F h hh t ht
  have htρ : t H.rt = ρ₀ := by
    apply RingOfIntegers.ext
    rw [ht, hρ₀ τ]
  exact ⟨hfin, hdeg.trans (hCM E H hH χ hχ K ρ₀ σ₁ Dw.p Dw.q X F h hh t htρ)⟩

end GlobalTheory.FlatCore
end

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_degree_cm_log_period : CMDiffSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → FrameDeg U x (GlobalTheory.CM.logOm E χ).re := by
  atlas_forward_decl GlobalTheory.FlatCore.frameDeg_of_cmDiff
end

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_constant_everywhere : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension → GlobalTheory.Published.PrismaticDieudonneHodge → Always fun U x => HTConst U x := by
  first | exact @GlobalTheory.FlatCore.htConst_always | exact GlobalTheory.FlatCore.htConst_always | (intros; apply GlobalTheory.FlatCore.htConst_always <;> assumption)
end

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G GlobalTheory.Frames GlobalTheory.HTLat
open scoped NNReal

namespace GlobalTheory.EmbOnto

theorem embAt_surj {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (C : Type) [Field C] [IsAlgClosed C] [CharZero C] [Algebra c.F C] (φ : E →+* C) :
    ∃ σ : E →+* ℂ, embAt c C σ = φ := by
  have hinj : Function.Injective (fun σ : E →+* ℂ => embAt c C σ) := by
    intro σ τ h
    ext a
    have h1 : embF c σ a = embF c τ a := (algebraMap c.F C).injective (DFunLike.congr_fun h a)
    have h2 := congrArg (fun x : c.F => (x : ℂ)) h1
    exact h2
  have hb := Function.Injective.bijective_of_nat_card_le hinj (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, NumberField.Embeddings.card,
      NumberField.Embeddings.card])
  exact hb.2 φ

end GlobalTheory.EmbOnto
end

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G GlobalTheory.Frames GlobalTheory.HTLat
open scoped NNReal

namespace GlobalTheory

theorem placeBelow_exists {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}
    (c : Coeff l) (σ : E →+* ℂ) (la : HeightOneSpectrum (𝓞 c.F)) : ∃ w : HeightOneSpectrum (𝓞 E),
      ∀ a : 𝓞 E, a ∈ w.asIdeal ↔ la.valuation c.F (embK c σ a) < 1 := by
  set f : 𝓞 E →+* 𝓞 c.F := RingOfIntegers.mapRingHom (embF c σ) with hf
  have hemb : ∀ a : 𝓞 E, embK c σ a = algebraMap (𝓞 c.F) c.F (f a) := fun _ => rfl
  obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot la.ne_bot
  have hZ : Ideal.comap (algebraMap ℤ (𝓞 c.F)) la.asIdeal ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hx0 hxI (Algebra.IsIntegral.isIntegral x)
  obtain ⟨n, hnI, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hZ
  haveI : la.asIdeal.IsPrime := la.isPrime
  refine ⟨⟨la.asIdeal.comap f, Ideal.comap_isPrime f la.asIdeal, ?_⟩, fun a => ?_⟩
  · intro hbot
    have hmem : ((n : ℤ) : 𝓞 E) ∈ la.asIdeal.comap f := by
      rw [Ideal.mem_comap, map_intCast]
      simpa using hnI
    rw [hbot, Ideal.mem_bot] at hmem
    exact hn0 (by exact_mod_cast hmem)
  · show f a ∈ la.asIdeal ↔ _
    rw [hemb, HeightOneSpectrum.valuation_lt_one_iff_mem]

end GlobalTheory
end

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G GlobalTheory.Frames GlobalTheory.HTLat
open scoped NNReal

namespace GlobalTheory.CompHt

theorem norm_algebraMap_lt_one_iff_valuation_lt_one : ∀ (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (ℓ : ℕ) [Fact ℓ.Prime]
    [Algebra K ℂ_[ℓ]], (ℓ : 𝓞 K) ∈ la.asIdeal → ∀ (T : CDVR) (io : K →+* T.Fr) (e : ℕ), OverLa la T.V io e →
    ∀ (k : T.Fr →+* ℂ_[ℓ]), (∀ b, k (io b) = algebraMap K ℂ_[ℓ] b) →
      (∀ x : T.Fr, val_vw la ℓ (Valued.v : Valuation ℂ_[ℓ] ℝ≥0) (k x) = nval T.V e x) →
      ∀ b : K, ‖algebraMap K ℂ_[ℓ] b‖ < 1 ↔ la.valuation K b < 1 := by
  intro K _ _ la ℓ _ _ hℓ T io e ho k hk hm b
  have hnv : ∀ x : ℂ_[ℓ], ‖x‖ = ((Valued.v x : ℝ≥0) : ℝ) := fun x => by
    rw [PadicComplex.norm_eq_norm, Valuation.norm_def, PadicComplex.RankOne.hom_eq_embedding,
      Valuation.embedding_restrict]
  by_cases hb : b = 0
  · subst hb; simp

  have hpos : ∀ x : K, x ≠ 0 → (0 < vLa la x ↔ la.valuation K x < 1) := fun x hx => by
    have h0 : la.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
    have := WithZero.log_lt_log h0 (one_ne_zero)
    rw [WithZero.log_one] at this
    simp only [vLa]
    constructor
    · intro h; exact this.1 (by omega)
    · intro h; have := this.2 h; omega
  have hℓK : (ℓ : K) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  have hcpos : (0 : ℝ) < vLa la (ℓ : K) := by
    have h1 : la.valuation K (ℓ : K) < 1 := by
      have := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) la (ℓ : 𝓞 K)).2 hℓ
      simpa using this
    exact_mod_cast (hpos _ hℓK).2 h1
  have ha : algebraMap K ℂ_[ℓ] b ≠ 0 := (map_ne_zero _).2 hb
  have hio : io b ≠ 0 := (map_ne_zero _).2 hb
  have h := hm (io b)
  rw [hk, val_vw_of_ne la ℓ _ ha, nval_of_ne hio, ho.2 b] at h
  have he : (e : ℝ) ≠ 0 := by exact_mod_cast ho.1.ne'
  have h' : (vLa la (ℓ : K) : ℝ) * (Real.log ((Valued.v : Valuation ℂ_[ℓ] ℝ≥0) (algebraMap K ℂ_[ℓ] b) : ℝ) /
      Real.log ((Valued.v : Valuation ℂ_[ℓ] ℝ≥0) (ℓ : ℂ_[ℓ]) : ℝ)) = vLa la b := by
    rw [EReal.coe_eq_coe_iff] at h
    rw [h]; push_cast; field_simp
  have hL : Real.log ((Valued.v : Valuation ℂ_[ℓ] ℝ≥0) (ℓ : ℂ_[ℓ]) : ℝ) < 0 := by
    rw [PadicComplex.valuation_p]
    have : (1 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
    push_cast
    exact Real.log_neg (by positivity) (by rw [one_div]; exact inv_lt_one_of_one_lt₀ this)
  have hva : (0 : ℝ) < ((Valued.v : Valuation ℂ_[ℓ] ℝ≥0) (algebraMap K ℂ_[ℓ] b) : ℝ) := by
    have : (Valued.v : Valuation ℂ_[ℓ] ℝ≥0) (algebraMap K ℂ_[ℓ] b) ≠ 0 := (Valuation.ne_zero_iff _).2 ha
    exact_mod_cast pos_iff_ne_zero.2 this
  rw [hnv, ← hpos b hb, ← Int.cast_pos (R := ℝ), ← h', mul_pos_iff_of_pos_left hcpos,
    ← Real.log_neg_iff hva]
  constructor
  · intro hA; exact div_pos_of_neg_of_neg hA hL
  · intro hq
    by_contra hA; push_neg at hA
    exact absurd hq (not_lt.2 (div_nonpos_of_nonneg_of_nonpos hA hL.le))

end GlobalTheory.CompHt
end

section
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G GlobalTheory.Frames GlobalTheory.HTLat
open scoped NNReal

namespace GlobalTheory.CompHt

open GlobalTheory.HodgeTateCompare GlobalTheory.EigenLieCompare GlobalTheory.EigenSplit GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel ReciprocityTheory.ChartRestriction.G.Pdiv TensorProduct in

theorem finrank_eigW_embInt_eq_mult : GlobalTheory.CovTop.Hypotheses2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
    [Algebra c.F C] [StarRing (𝓞 E)] (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), y₀.IsAlg →
    ∀ (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] C) (kO : T.V →+* O) (P : Point p v O (𝓞 E))
      (ψ : P.A.A.left ⟶ Xo.univ.t.G.left) (z : FrPt Xo c C),
      (letI := io.toAlgebra; PointOver P y₀.1.x k.toRingHom kO ψ) → (letI := io.toAlgebra; FrMap k y₀.1 z) →
      ∀ σ : E →+* ℂ, Module.finrank C (P.eigW (embInt c P.integers σ)) = Dw.mult σ := by
  intro hPr E _ _ _ H Dw l Xo c p _ C _ _ _ v O _ _ _ _ _ _ _ _ _ T io y₀ hy k kO P ψ z hPO hFr σ
  obtain ⟨-, -, hcok, hshape⟩ := GlobalTheory.HTKernel.hodgeTateKernelAtPoint hPr p C v O (𝓞 E) P
  have hW : P.W = Submodule.span C (Set.range P.bLie) := hshape.2.2.2.2.2.2
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  haveI : ValuationRing O := ValuationRing.of_integers v P.integers
  haveI : IsFractionRing O C := P.integers.isFractionRing
  haveI := (GlobalTheory.UnitRigidity.smooth_geometricallyConnected_of_isGt _ _ ⟨P.D⟩).1
  obtain ⟨-, -, hb⟩ := Point.omega_free_finite_bijective p C v O (𝓞 E) P
  have hp : algebraMap O C ((p : O) ^ 2) ≠ 0 := by
    rw [map_pow, map_natCast]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hinj : Function.Injective P.bLie := by
    intro x y hxy
    have h0 : ∀ t, (P.al₀ t).1 x = (P.al₀ t).1 y := fun t => P.integers.hom_inj (by
      rw [← P.pairV_bLie, ← P.pairV_bLie, hxy])
    have h1 : ∀ z, (P.al z).1 x = (P.al z).1 y := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z z' hz hz' => simp only [map_add, Submodule.coe_add, Pi.add_apply, hz, hz']
      | tmul c t => simp only [Point.al_tmul, Submodule.coe_smul, Pi.smul_apply, h0]
    refine hb.1 (LinearMap.ext fun f => ?_)
    obtain ⟨z, hz⟩ := hcok f
    have h2 := h1 z
    rw [hz] at h2
    exact mul_left_cancel₀ (fun h => hp (by rw [h, map_zero])) h2
  have hE : P.eigW (embInt c P.integers σ) =
      Submodule.span C (P.wRec (embInt c P.integers σ) : Set P.V) := by
    refine le_antisymm ?_ (Submodule.span_le.2 fun w hw => ?_)
    · rintro w ⟨hw, hwτ⟩
      rw [hW] at hw
      obtain ⟨s, hs, x, hx⟩ := GlobalTheory.HodgeTateEigenRank.exists_smul_mem_of_mem_span (C := C) P.latLie hw
      have hs' : algebraMap O C s ≠ 0 := fun h => hs (P.integers.hom_inj (by rw [h, map_zero]))
      have hxτ : P.bLie x ∈ P.eigV (embInt c P.integers σ) := by
        rw [hx, ← algebraMap_smul C s]
        exact Submodule.smul_mem _ _ hwτ
      have hx' : AvDefs.IsEig P.Gt P.oGt (embInt c P.integers σ) x := fun a => hinj (by
        rw [P.bLie_act, P.bLie_scale, mem_eigenSub.1 hxτ a, RingHom.comp_apply, algebraMap_smul])
      have : w = (algebraMap O C s)⁻¹ • P.bLie x := by
        rw [hx, ← algebraMap_smul C s, smul_smul, inv_mul_cancel₀ hs', one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨x, hx'⟩, rfl⟩)
    · have h := P.wRec_le _ hw
      refine ⟨?_, h.2⟩
      rw [hW]
      exact Submodule.subset_span h.1
  obtain ⟨x, hx⟩ := TieFrame.exists_lieTie_of_frMap E H Dw l Xo c p C v O T io y₀ k kO P ψ z hPO hFr
  have hli := linearIndependent_evLie_of_lieTie E H Dw l Xo c p C v O T io y₀ k kO P ψ z hPO hFr σ (x σ) (hx σ)
  have hht : HTChar p v P.Gt := by
    letI := io.toAlgebra
    exact htChar_of_pointOver E H Dw l Xo c p C v O T io y₀ hy k.toRingHom kO P ψ hPO
  have hbl := (alC_surjective_and_linearIndependent_bLie p C v O (𝓞 E) P hht).2 _ _ hli
  have hsp := RecSpan.span_bLie_eq_wRec E H Dw l Xo c p C v O T io y₀ k kO P ψ z hPO hFr σ (x σ) (hx σ)
  rw [hE, ← hsp, Submodule.span_span_of_tower, finrank_span_eq_card hbl, Fintype.card_fin]

end GlobalTheory.CompHt
end
end

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G GlobalTheory.Frames GlobalTheory.HTLat
open scoped NNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pdiv_point_valuation_property : GlobalTheory.CovTop.Hypotheses2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
    [Algebra c.F C] [StarRing (𝓞 E)] (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), y₀.IsAlg →
    ∀ (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] C) (kO : T.V →+* O) (P : Point p v O (𝓞 E))
      (ψ : P.A.A.left ⟶ Xo.univ.t.G.left) (z : FrPt Xo c C),
      (letI := io.toAlgebra; PointOver P y₀.1.x k.toRingHom kO ψ) → (letI := io.toAlgebra; FrMap k y₀.1 z) →
      ∀ σ : E →+* ℂ, Module.finrank C (P.eigW (embInt c P.integers σ)) = Dw.mult σ := by
  atlas_forward_decl GlobalTheory.CompHt.finrank_eigW_embInt_eq_mult
end

section
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G GlobalTheory.Frames GlobalTheory.HTLat
open scoped NNReal

namespace GlobalTheory.HTShiftPf

attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

theorem prime_mem {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 K) ∈ la.asIdeal := by
  have : Finite (𝓞 K ⧸ la.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot la.asIdeal la.ne_bot
  have : la.asIdeal.IsMaximal := la.isMaximal
  let _ : Field (𝓞 K ⧸ la.asIdeal) := Ideal.Quotient.field _
  refine ⟨ringChar (𝓞 K ⧸ la.asIdeal), CharP.char_is_prime (𝓞 K ⧸ la.asIdeal) _, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem prime_unique {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (h1 : (p : 𝓞 K) ∈ la.asIdeal) (h2 : (q : 𝓞 K) ∈ la.asIdeal) : p = q := by
  by_contra hne
  obtain ⟨a, b, hab⟩ : IsCoprime (p : 𝓞 K) (q : 𝓞 K) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  exact la.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)))

theorem norm_eq_v (p : ℕ) [Fact p.Prime] (x : ℂ_[p]) : ‖x‖ = ((Valued.v x : ℝ≥0) : ℝ) := by
  rw [PadicComplex.norm_eq_norm, Valuation.norm_def, PadicComplex.RankOne.hom_eq_embedding,
    Valuation.embedding_restrict]

open Classical in

theorem htShift : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.FlatCM.PlaceShiftSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H →
    ∀ (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), HTShift Xo c := by
  intro hP2 hPS E _ _ _ H hH Dw l Xo c τ la
  obtain ⟨ℓ, hℓ, hℓla⟩ := prime_mem la
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨w, hw⟩ := GlobalTheory.placeBelow_exists c τ.1 la
  obtain ⟨κ₁, κ₂, hκ⟩ := hPS E H hH ℓ w
  refine ⟨(vLa la (ℓ : c.F) : ℝ) * (-((Dw.mult τ.1 : ℝ) * κ₁ + (Dw.mult (conjEmb τ.1) : ℝ) * κ₂) /
    Real.log ((Valued.v (ℓ : ℂ_[ℓ]) : ℝ≥0) : ℝ)), ?_⟩
  intro T io e y₀ ho hAlg wv hwv f hf
  obtain ⟨p, hp, _, k, y, hy, rfl⟩ := hwv
  obtain rfl : p = ℓ := prime_unique hp.out hℓ (hy.mem ho) hℓla
  letI := H.starRing
  letI := io.toAlgebra
  have hy' : IsHTFrame p (Valued.v : Valuation ℂ_[p] ℝ≥0) 𝓞_ℂ_[p] y₀ k y := hy
  have hm := hy'.val_vw_map ho
  obtain ⟨-, kO, P, ψ, z, hPO, hz, g, a, x, hfc, hg, ha, hx, hb⟩ := hy'
  have hdet : ∀ σ, IsUnit (g σ).det := fun σ =>
    (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1
      (LinearIndependent.of_comp (Fintype.linearCombination ℂ_[p] fun j => P.bLie (x σ j)) (hb σ).1))
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  have hA := GlobalTheory.FlatFrameLaw.evR_flat_frChg τ hf g a z y hfc hg hdet ha0
  have hB : evR Xo c f z = k (evI y₀ f) := GlobalTheory.FlagTan.evR_frMap hf.1 hz

  have hs : ∀ a : 𝓞 E, star a = H.bar a := fun _ => rfl
  have hplace : ∀ a : 𝓞 E, a ∈ w.asIdeal ↔ ‖embAt c ℂ_[p] τ.1 (a : E)‖ < 1 := fun a => by
    rw [hw, embAt, RingHom.comp_apply]
    exact (GlobalTheory.CompHt.norm_algebraMap_lt_one_iff_valuation_lt_one c.F la p hℓla T io e ho k.toRingHom (fun b => k.commutes b) hm _).symm
  have hsig : ∀ φ : E →+* ℂ_[p], Module.finrank ℂ_[p] (P.eigW (embO P.integers φ)) =
      if φ (H.rt : E) = embAt c ℂ_[p] τ.1 (H.rt : E) then Dw.mult τ.1 else Dw.mult (conjEmb τ.1) := fun φ => by
    obtain ⟨σ, rfl⟩ := GlobalTheory.EmbOnto.embAt_surj c ℂ_[p] φ
    have e1 := GlobalTheory.T.pdiv_point_valuation_property hP2 E H Dw l Xo c p ℂ_[p] Valued.v 𝓞_ℂ_[p] T io y₀ hAlg k kO P ψ z hPO hz σ
    refine e1.trans ?_
    have hinj : σ (H.rt : E) = τ.1 (H.rt : E) ↔ embAt c ℂ_[p] σ (H.rt : E) = embAt c ℂ_[p] τ.1 (H.rt : E) := by
      constructor
      · intro h
        simp only [embAt, RingHom.comp_apply]
        congr 1
        exact Subtype.ext h
      · intro h
        simp only [embAt, RingHom.comp_apply] at h
        exact congrArg Subtype.val ((algebraMap c.F ℂ_[p]).injective h)
    rw [Datum.mult, Datum.mult, Datum.mult, if_pos τ.2, if_neg (conj_not_mem τ), ← hinj, τ.2]
  have hs1 := GlobalTheory.CompHt.RecSpan.span_bLie_eq_wRec E H Dw l Xo c p ℂ_[p] Valued.v 𝓞_ℂ_[p] T io y₀ k kO P ψ z hPO hz
    τ.1 (x τ.1) (hx τ.1)
  have hs2 := GlobalTheory.CompHt.RecSpan.span_bLie_eq_wRec E H Dw l Xo c p ℂ_[p] Valued.v 𝓞_ℂ_[p] T io y₀ k kO P ψ z hPO hz
    (conjEmb τ.1) (x (conjEmb τ.1)) (hx (conjEmb τ.1))
  rw [embInt_conj hs] at hs2
  have hb1 := hb τ.1
  rw [htLat_psi P τ] at hb1
  have hb2 := hb (conjEmb τ.1)
  rw [htLat_conj P τ, embInt_conj hs] at hb2
  have hlog := hκ (embAt c ℂ_[p] τ.1) hplace P (Dw.mult τ.1) (Dw.mult (conjEmb τ.1)) hsig (x τ.1) (x (conjEmb τ.1))
    (g τ.1) (g (conjEmb τ.1)) hs1 hs2 hb1 hb2
  rw [norm_eq_v, norm_eq_v] at hlog

  have hd1 : (g τ.1).det ≠ 0 := (hdet τ.1).ne_zero
  have hd2 : (g (conjEmb τ.1)).det ≠ 0 := (hdet (conjEmb τ.1)).ne_zero
  show val_vw la p Valued.v (evR Xo c f y) = _
  rw [hA, hB, val_vw_mul, val_vw_mul, hm, val_vw_of_ne la p _ (inv_ne_zero hd1), val_vw_of_ne la p _ hd2,
    ← EReal.coe_add, add_comm]
  congr 2
  rw [map_inv₀, NNReal.coe_inv, Real.log_inv, ← hlog]
  ring

end GlobalTheory.HTShiftPf

end
end

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_shift_cm : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.FlatCM.PlaceShiftSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), HTShift Xo c := by
  atlas_forward_decl GlobalTheory.HTShiftPf.htShift
end

section
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.FlatCore

theorem flatDegreeSt_of_prismaticDieudonne :
    GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne →
      GlobalTheory.Published.DeRhamCanonicalExtension → GlobalTheory.Published.PrismaticDieudonneHodge → FlatDegreeSt := by
  intro hSW hP2 hQ2 hQ3 hPD
  intro E _ _ _ H hH _ χ hχ Dw l Xo c r U x hL
  have hPS : GlobalTheory.FlatCM.PlaceShiftSt := GlobalTheory.placeShiftSt_of_scholzeWeinstein hP2 hSW
  have hCM : CMDiffSt := GlobalTheory.T.cm_different_from_ideal (GlobalTheory.T.ideal_from_place_shift hPS)
  have hArch : ArchEx U x := GlobalTheory.T.archimedean_existence_everywhere E H Dw l Xo c r U x hL
  have hHT : HTConst U x := GlobalTheory.T.hodge_tate_constant_everywhere hP2 hQ2 hQ3 hPD E H Dw l Xo c r U x hL
  have hSh : HTShift Xo c := GlobalTheory.T.hodge_tate_shift_cm hP2 hPS E H hH Dw l Xo c
  have hFin : FinConst U x := GlobalTheory.FlatCore.Fin.finConst_main E H Dw l Xo c r U x hL hSh hHT
  have hFr : FrameDeg U x (GlobalTheory.CM.logOm E χ).re := GlobalTheory.T.frame_degree_cm_log_period hCM E H hH χ hχ Dw l Xo c r U x hL
  exact GlobalTheory.FlatCore.flatDegree_of_steps E H Dw l Xo c r U x hL _ hArch hFin hFr

end GlobalTheory.FlatCore
end

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_degree_from_prismatic : GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension → GlobalTheory.Published.PrismaticDieudonneHodge → FlatDegreeSt := by
  atlas_forward_decl GlobalTheory.FlatCore.flatDegreeSt_of_prismaticDieudonne
end
