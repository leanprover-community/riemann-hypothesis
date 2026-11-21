import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormPlus
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LiesOverFramedOfSquareLevelMoves
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsConjLevelMapByLevelMoves
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsQuotEquiv
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameFreeFiniteOrderRuleConstPeriodSpace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ComponentAttainedAtBaseFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NegIndexTransposeOfHasSignature
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAdelicUnitaryOfLatticeIsometries
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MarkedLatticeIsometryDoubleCosetMove
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCompletedIsometryInducingHalfLevelAutomorp
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ActLevFullLevelGroupFramedPointsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePointsStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelAutomorphismPeriodFamily
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComplexFrobeniusPoints
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LiftDatumAlternatingFormSignEqOneStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ComponentEqOfMatchedLatticesMarkings
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoverMulShortThetaSeriesIndepOfFramedLift
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortValTotOfPinned

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liesOverFramed_of_square_levelMoves : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (ρ₂ : d.Xo₂.X ⟶ d.Xo₂.X) (ν₂ : SABMap d.Xo₂.univ.t d.Xo₂.univ.t ρ₂) (r' : d.Xo₂.X ⟶ Xo.X) (m' : SABMap d.Xo₂.univ.t Xo.univ.t r'), ρ₂ ≫ r' = d.r ≫ ρ → ν₂.φ ≫ m'.φ = d.m.φ ≫ ν.φ → ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S] (y y' : FrPt Xo c S) (y₂ y₂' : FrPt d.Xo₂ d.c₂ S), FrOver d y₂ y → FrMove ρ ν y y' → FrMove ρ₂ ν₂ y₂ y₂' → FrOver { d with r := r', m := m' } y₂' y' := by
  first | exact @GlobalTheory.frOver_of_square_of_frMove | exact GlobalTheory.frOver_of_square_of_frMove | (intros; apply GlobalTheory.frOver_of_square_of_frMove <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_levelMap_by_levelMoves : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.EtaOK → ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (ρ₂ : d.Xo₂.X ≅ d.Xo₂.X) (ν₂ : SABMap d.Xo₂.univ.t d.Xo₂.univ.t ρ₂.hom) (gM gA gM₂ gA₂ : Dw.La →ₗ[𝓞 E] Dw.La), IsLevMove ρ ν gM gA → IsLevMove ρ₂.hom ν₂ gM₂ gA₂ → (∀ a, gM₂ a - gM a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ a, Dw.ModN l.A (gA₂ a - gA a)) → ∃ (r' : d.Xo₂.X ⟶ Xo.X) (m' : SABMap d.Xo₂.univ.t Xo.univ.t r'), ρ₂.hom ≫ r' = d.r ≫ ρ ∧ ν₂.φ ≫ m'.φ = d.m.φ ≫ ν.φ ∧ DeltaDat.EtaOK { d with r := r', m := m' } := by
  first | exact @GlobalTheory.exists_conj_levelMap | exact GlobalTheory.exists_conj_levelMap | (intros; apply GlobalTheory.exists_conj_levelMap <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DatumCoverAdjoint

open GlobalTheory.DatumInverseCharacter

theorem span_image_sup_eq_top {R M J : Type} [CommRing R] [AddCommGroup M] [Module R M] (K : Ideal R)
    (φ : M →ₗ[R] M) (hφ : ∀ a, ∃ b, φ b - a ∈ (K • ⊤ : Submodule R M)) (x : J → M) (s : Set J)
    (h : Submodule.span R (x '' s) ⊔ (K • ⊤ : Submodule R M) = ⊤) :
    Submodule.span R ((fun i => φ (x i)) '' s) ⊔ (K • ⊤ : Submodule R M) = ⊤ := by
  rw [eq_top_iff]
  intro a _
  obtain ⟨b, hb⟩ := hφ a
  have h1 : φ b ∈ Submodule.map φ (Submodule.span R (x '' s) ⊔ (K • ⊤ : Submodule R M)) :=
    Submodule.mem_map_of_mem (by rw [h]; exact Submodule.mem_top)
  rw [Submodule.map_sup, Submodule.map_span, Set.image_image, Submodule.map_smul''] at h1
  have h2 : φ b ∈ Submodule.span R ((fun i => φ (x i)) '' s) ⊔ (K • ⊤ : Submodule R M) :=
    SetLike.le_def.1 (sup_le_sup le_rfl (Submodule.smul_mono le_rfl le_top)) h1
  have := sub_mem h2 (Submodule.mem_sup_right hb)
  rwa [sub_sub_cancel] at this

theorem datum_adjoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.l₂.M = l.M * d.pd → d.l₂.Mb = l.Mb * d.I → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d), d.PhiPin ph ψ x₀ → ∀ g : Sim Dw, (∀ a, g.f d.l₂.M a - a ∈ d.I • (⊤ : Submodule (𝓞 E) Dw.La)) → ∃ σq : LevQ Dw d.l₂ ≃ LevQ Dw d.l₂, (∀ a, σq (Submodule.Quotient.mk a) = Submodule.Quotient.mk (g.f d.l₂.M a)) ∧ ∀ (rk : Bool) (x0 : Fin n → Dw.La), AdmX (l := l) rk x0 → ∃ x0' : Fin n → Dw.La, AdmX (l := l) rk x0' ∧ ∀ q : Fin n → LevQ Dw d.l₂, d.w x0 (fun b => σq.symm (q b)) = d.w x0' q := by
  intro E _ _ _ H Dw l Xo c n d hM hb ph ψ x₀ hpin g hg
  obtain ⟨-, -, -, -, -, hφ⟩ := hpin
  have hM₂ : 0 < d.l₂.M := by have := d.l₂.three_le; omega
  have hM₁ : 0 < l.M := by have := l.three_le; omega
  have hpd : 0 < d.pd := Nat.pos_of_mul_pos_left (hM ▸ hM₂)
  have hIJ := half_prod hM hb
  have hspan : ∀ (l' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H),
      ((l'.M : ℕ) : 𝓞 E) ∈ l'.Mb * l'.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := fun l' => by
    rw [l'.prod]; exact Ideal.mem_span_singleton_self _
  have hbI : d.l₂.Mb ≤ d.I := hb ▸ (Ideal.mul_le_inf.trans inf_le_right)
  have hbM : d.l₂.Mb ≤ l.Mb := hb ▸ (Ideal.mul_le_inf.trans inf_le_left)
  have hmb : ((d.l₂.M : ℕ) : 𝓞 E) ∈ d.l₂.Mb := (Ideal.mul_le_inf.trans inf_le_left) (hspan d.l₂)
  have hmJ : ((d.l₂.M : ℕ) : 𝓞 E) ∈ Mfr l :=
    Ideal.map_mono hbM ((Ideal.mul_le_inf.trans inf_le_right) (hspan d.l₂))
  obtain ⟨g', hg'⟩ := g.inv d.l₂.M hM₂
  set f := g.f d.l₂.M with hf
  obtain ⟨σ, hσ⟩ := exists_quot_equiv Dw hmb f g' hg'
  obtain ⟨fa, hfa⟩ := exists_adjoint Dw f
  obtain ⟨ga, hga⟩ := exists_adjoint Dw g'
  have hsurj : ∀ a, ∃ b, ga b - a ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La) := fun a =>
    ⟨fa a, mem_of_modN Dw hmJ (modN_of_dvd Dw hM₂ fun v => by
      rw [map_sub, LinearMap.sub_apply, hga, hfa, ← map_sub]
      exact dvd_of_modN Dw a (hg' v).2)⟩
  refine ⟨σ.toEquiv, hσ, fun rk x0 hx => ⟨fun b => ga (x0 b),
    span_image_sup_eq_top (Mfr l) ga hsurj x0 _ hx, fun q => ?_⟩⟩
  have hq : ∀ b, f (levRep (σ.toEquiv.symm (q b))) - levRep (q b) ∈ (d.l₂.Mb • ⊤ : Submodule (𝓞 E) Dw.La) := by
    intro b
    rw [← Submodule.Quotient.eq, ← hσ, levRep_spec, levRep_spec]
    exact σ.apply_symm_apply _
  have hz : zetaM c ^ pairL (l := l) x0 (fun b => levRep (σ.toEquiv.symm (q b))) =
      zetaM c ^ pairL (l := l) (fun b => ga (x0 b)) (fun b => levRep (q b)) := by
    refine zpow_congr hM₁ (root_pow c dvd_rfl) ?_
    unfold pairL
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun b _ => ?_
    rw [hga, g'.map_smul, ← map_sub, ← smul_sub]
    refine dvd_right Dw l.prod (cSep_mem l) _ ?_
    set a := levRep (σ.toEquiv.symm (q b))
    have h1 : g' (f a - levRep (q b)) ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La) := by
      have := Submodule.mem_map_of_mem (f := g') (hq b)
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono hbM le_top this
    have h2 : g' (f a) - a ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La) :=
      mem_of_modN Dw (hbM hmb) (hg' a).1
    have := sub_mem h1 h2
    convert this using 1
    rw [map_sub]
    abel
  have hroot := root_pow d.c₂ (N := d.pd) (hM ▸ Dvd.intro_left _ rfl)
  have hδ : d.eF (d.φδ (fun b => σ.toEquiv.symm (q b))) = d.eF (d.φδ q) := by
    rw [hφ, hφ]
    refine finsum_congr fun x => ?_
    congr 1
    refine zpow_congr hpd hroot ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun b _ => ?_
    rw [← map_sub, ← smul_sub]
    refine dvd_right Dw hIJ (cHalf_mem d.I) _ ?_
    have := sub_mem (Submodule.smul_mono hbI le_rfl (hq b)) (hg (levRep (σ.toEquiv.symm (q b))))
    convert this using 1
    abel
  unfold DeltaDat.w
  rw [hz, map_mul, map_mul, hδ]

end GlobalTheory.DatumCoverAdjoint
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCoverDatum_similitude_adjoint_transport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.l₂.M = l.M * d.pd → d.l₂.Mb = l.Mb * d.I → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d), d.PhiPin ph ψ x₀ → ∀ g : Sim Dw, (∀ a, g.f d.l₂.M a - a ∈ d.I • (⊤ : Submodule (𝓞 E) Dw.La)) → ∃ σq : LevQ Dw d.l₂ ≃ LevQ Dw d.l₂, (∀ a, σq (Submodule.Quotient.mk a) = Submodule.Quotient.mk (g.f d.l₂.M a)) ∧ ∀ (rk : Bool) (x0 : Fin n → Dw.La), AdmX (l := l) rk x0 → ∃ x0' : Fin n → Dw.La, AdmX (l := l) rk x0' ∧ ∀ q : Fin n → LevQ Dw d.l₂, d.w x0 (fun b => σq.symm (q b)) = d.w x0' q := by
  first | exact @GlobalTheory.DatumCoverAdjoint.datum_adjoint | exact GlobalTheory.DatumCoverAdjoint.datum_adjoint | (intros; apply GlobalTheory.DatumCoverAdjoint.datum_adjoint <;> assumption)
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct
open GlobalTheory.ShortMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameFree_finiteOrder_rule_const_periodSpace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (f : Rul Xo c), f ∈ sec Xo c 0 0 → (∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (y y' : FrPt Xo c K), y'.x = y.x → evR Xo c f y' = evR Xo c f y) → (∃ N : ℕ, 0 < N ∧ ∀ y : FrPt Xo c (CAt σ), evR Xo c f y ^ N = 1) → ∀ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H Dw.p Dw.q ty → ∀ (i : Fin F.n) (P P' : (F.Di i).La →+ (Fin g → ℂ)) (y y' : FrPt Xo c (CAt σ)), IsPeriod (F.Di i) ty P → IsPeriod (F.Di i) ty P' → y.x = F.u i P → y'.x = F.u i P' → evR Xo c f y = evR Xo c f y' := by
  first | exact @GlobalTheory.FiniteOrderConst.const_on_period_space | exact GlobalTheory.FiniteOrderConst.const_on_period_space | (intros; apply GlobalTheory.FiniteOrderConst.const_on_period_space <;> assumption)
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct
open GlobalTheory.ShortMove

namespace GlobalTheory.ShortMove

open scoped Matrix nonZeroDivisors
open GlobalTheory.RecDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_marked_of_component : ∀ (D : D7) (V : HSp D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)) (F : FamilyUnif Xo σ' ty), IsTypeFn H Dw.p Dw.q ty → ∀ (r : ℕ) (hr : V.rank = r) (X : Data D.host.E r) (i : Fin F.n) (φ : (F.Di i).La ≃ₗ[𝓞 D.host.E] X.Λ) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), ModelW V hr X → (∀ a b, (((F.Di i).EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-X.ξ0 * herm X.Gm (φ a : Fin r → D.host.E) (φ b))) → LatEmb V io → FormPlus V io → ∃ h : GA D V, Marked V hr io l X.Λ (fun a => (φ (F.t i a) : Fin r → D.host.E)) h := by
  intro D V H Dw l Xo σ' g ty F hty r hr X k φ io hW hef hemb hform
  subst hr
  obtain ⟨hinj, hrange⟩ := hemb
  have hEF : ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-(-D.host.xi0) *
      herm (gmW V rfl) (io x) (io y)) := by
    intro x y
    have h := trace_herm_gmW V rfl (V.frame.equivFun.symm (io x)) (V.frame.equivFun.symm (io y))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
    rw [hform, neg_neg, ← h]
    rfl
  obtain ⟨-, P, hP⟩ := (PeriodExists.typeFn_period_exist _ H (F.Di k)).2.1 g ty
    (by rw [(F.sig k).1, (F.sig k).2]; exact hty)
  obtain ⟨f, h1, h2, h3, h4⟩ := familyUnif_lattice_genus _ H Dw l Xo σ' g ty F k P hP
  let c : D.host.E ≃ₐ[D.host.F] D.host.E :=
    AlgEquiv.ofAlgHom D.sp.cm.sig D.sp.cm.sig (AlgHom.ext fun x => star_star x) (AlgHom.ext fun x => star_star x)
  obtain ⟨hfg, hsp, hlat⟩ := comp_latG D V
  rw [← hrange] at hfg hsp hlat
  have hξ : -(-D.host.xi0) ≠ 0 := by
    rw [← hW.2]
    exact neg_ne_zero.2 X.ξ0_ne
  obtain ⟨gf, hg1, hg2, hg3⟩ := comp_adelic_of_tower D.host.F D.host.E V.rank c (-V.gram.transpose)
    (-(-D.host.xi0)) hξ Dw.La (F.Di k).La (fun x y => Dw.EF x y) (fun x y => (F.Di k).EF x y) io hinj
    X.Λ φ hfg hsp X.Λ_fg X.Λ_span hEF
    (fun x y => by
      have := hef x y
      rw [hW.1, hW.2] at this
      exact this) f h1 h2 h3
  obtain ⟨u, hu, hug⟩ := (GlobalTheory.T.adelicUnitary_exists_with_prescribed_parts D V).1 gf (comp_mem_HR _ _ _ c _ (fun _ => rfl) _ gf hg3)
  have hc := (AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank X.Λ X.Λ_fg
    X.Λ_span).1
  refine ⟨u, ?_, fun a ha => ?_⟩
  · rw [(hlat u).1, hug]
    refine Eq.trans ?_ (Set.image_id _).symm
    ext v
    rw [AdLat.latOf, hg1]
    exact (hc v).symm
  · obtain ⟨e, he⟩ := h4 a ha
    obtain ⟨w, hw, hgw⟩ := hg2 l.M (lt_of_lt_of_le (by norm_num) l.three_le) a
    have hmem : ∀ z, z ∈ latGHat V u ↔ z ∈ AdLat.hat D.host.F (X.Λ : Set (Fin V.rank → D.host.E)) := by
      intro z
      rw [← SetLike.mem_coe, (hlat u).2, hug, hg1, SetLike.mem_coe]
    rw [hug]
    refine ⟨-(AdLat.fv D.host.F (φ e : Fin V.rank → D.host.E) + w),
      (hmem _).2 (neg_mem (add_mem ((hc _).2 (φ e).2) hw)), ?_⟩
    change AdLat.fv D.host.F (φ (F.t k a) : Fin V.rank → D.host.E) - gf.1 *ᵥ AdLat.fv D.host.F (io a) = _
    rw [hgw, he, map_add, map_nsmul, Submodule.coe_add, Submodule.coe_smul_of_tower, AdLat.cap_fv_add,
      AdLat.cap_fv_nsmul]
    exact comp_sub_eq _ _ _ _

end GlobalTheory.ShortMove
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct
open GlobalTheory.ShortMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_element_of_marked_component_lattice : ∀ (D : D7) (V : HSp D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)) (F : FamilyUnif Xo σ' ty), IsTypeFn H Dw.p Dw.q ty → ∀ (r : ℕ) (hr : V.rank = r) (X : Data D.host.E r) (i : Fin F.n) (φ : (F.Di i).La ≃ₗ[𝓞 D.host.E] X.Λ) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), ModelW V hr X → (∀ a b, (((F.Di i).EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-X.ξ0 * herm X.Gm (φ a : Fin r → D.host.E) (φ b))) → LatEmb V io → FormPlus V io → ∃ h : GA D V, Marked V hr io l X.Λ (fun a => (φ (F.t i a) : Fin r → D.host.E)) h := by
  first | exact @GlobalTheory.ShortMove.exists_marked_of_component | exact GlobalTheory.ShortMove.exists_marked_of_component | (intros; apply GlobalTheory.ShortMove.exists_marked_of_component <;> assumption)
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct
open GlobalTheory.ShortMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_unitary_of_lattice_isometries : ∀ (D : D7) (V : HSp D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), LatEmb V io → FormPlus V io → ∀ s : Sim Dw, (∀ n, s.ν n = 1) → ∃ κ : GA D V, latGHat V κ = latGHat V 1 ∧ ∀ N : ℕ, 0 < N → ∀ a, ∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (io a)) = finVec V (io (s.f N a)) + N • w := by
  first | exact @GlobalTheory.ShortMove.exists_adelic_of_isometry | exact GlobalTheory.ShortMove.exists_adelic_of_isometry | (intros; apply GlobalTheory.ShortMove.exists_adelic_of_isometry <;> assumption)
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct
open GlobalTheory.ShortMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.markedLattice_isometry_double_coset_move : ∀ (D : D7) (V : HSp D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (r : ℕ) (hr : V.rank = r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (X X' : Data D.host.E r) (A A' : Datum H) (φ : A.La ≃ₗ[𝓞 D.host.E] X.Λ) (φ' : A'.La ≃ₗ[𝓞 D.host.E] X'.Λ) (t : Dw.La →ₗ[𝓞 D.host.E] A.La) (t' : Dw.La →ₗ[𝓞 D.host.E] A'.La) (s : Dw.La →ₗ[𝓞 D.host.E] Dw.La) (h γ κ : GA D V), ModelW V hr X → ModelW V hr X' → (∀ a b, ((A.EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-X.ξ0 * herm X.Gm (φ a : Fin r → D.host.E) (φ b))) → (∀ a b, ((A'.EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-X'.ξ0 * herm X'.Gm (φ' a : Fin r → D.host.E) (φ' b))) → γ ∈ GQ V → latGHat V κ = latGHat V 1 → (∀ a, ∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (io a)) = finVec V (io (s a)) + l.M • w) → Marked V hr io l X.Λ (fun a => (φ (t a) : Fin r → D.host.E)) h → Marked V hr io l X'.Λ (fun a => (φ' (t' a) : Fin r → D.host.E)) (γ * h * κ) → ∃ gam : A.La ≃ₗ[𝓞 D.host.E] A'.La, (∀ a b, A'.EF (gam a) (gam b) = A.EF a b) ∧ ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ x, gam (t (s a)) = t' a + l.M • x := by
  first | exact @GlobalTheory.ShortMoveIso.marked_isometry | exact GlobalTheory.ShortMoveIso.marked_isometry | (intros; apply GlobalTheory.ShortMoveIso.marked_isometry <;> assumption)
end

section
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completed_isometry_inducing_half_level_automorphism : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l), ∃ g : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sim Dw, (∀ n, g.ν n = 1) ∧ (∀ x, (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ (g.f l.M x) = γ ((l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ x)) ∧ ∀ N : ℕ, 0 < N → Nat.Coprime N l.M → ∀ x, Dw.ModN N (g.f N x - x) := by
  first | exact @GlobalTheory.LevelIsometry.exists_isometry_inducing | exact GlobalTheory.LevelIsometry.exists_isometry_inducing | (intros; apply GlobalTheory.LevelIsometry.exists_isometry_inducing <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.ShortMove

section Adelic

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct

theorem exists_eq_nsmul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) {L : Type} [AddCommGroup L] [Module (𝓞 E) L] {x : L}
    (h₁ : x ∈ l.Mb • (⊤ : Submodule (𝓞 E) L)) (h₂ : x ∈ Mfr l • (⊤ : Submodule (𝓞 E) L)) : ∃ e, x = l.M • e := by
  have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ Mfr l := by rw [Mfr, l.coprime]; trivial
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h1
  have hp : l.Mb * Mfr l = Ideal.span {(l.M : 𝓞 E)} := l.prod
  have hx : x ∈ (Ideal.span {(l.M : 𝓞 E)} • ⊤ : Submodule (𝓞 E) L) := by
    have e : x = u • x + v • x := by rw [← add_smul, huv, one_smul]
    rw [e]
    refine add_mem ?_ ?_
    · rw [← hp, Submodule.mul_smul]
      exact Submodule.smul_mem_smul hu h₂
    · rw [← hp, mul_comm, Submodule.mul_smul]
      exact Submodule.smul_mem_smul hv h₁
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hx
  obtain ⟨e, -, he⟩ := hx
  exact ⟨e, by rw [← Nat.cast_smul_eq_nsmul (𝓞 E), he]⟩

theorem rdU_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    (f : Rul Xo c) (k : U.Comp) (x : Frame (U.X k).Ψ r) (h : rdU U f k x ≠ 0) :
    ∃ hx : x ∈ (U.X k).dom, rdU U f k x = toC (evR Xo c f (U.un k ⟨x, hx⟩)) := by
  have e : rdU U f k x = @dite _ (x ∈ (U.X k).dom) (Classical.propDecidable _)
      (fun h => toC (evR Xo c f (U.un k ⟨x, h⟩))) (fun _ => 0) := rfl
  by_cases hx : x ∈ (U.X k).dom
  · exact ⟨hx, by rw [e, dif_pos hx]⟩
  · exact absurd (by rw [e, dif_neg hx]) h

set_option maxHeartbeats 1000000 in

theorem exists_ratio {D : D7} (V : HSp D) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (hr : V.rank = r)
    (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hσ : GoodEmb c σ) (hA : l.A = 1) (hpq : 1 ≤ Dw.p + Dw.q)
    (hU : IsUnf U) (hW : ∀ k, ModelW V hr (U.X k)) (hD : DictLat U V hr dict io e F ik φ th x₀)
    (hL : LatEmb V io) (hF : FormPlus V io) (f : Rul Xo c) (hf : f ∈ sec Xo c 0 0)
    (hfree : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (y y' : FrPt Xo c K), y'.x = y.x →
      evR Xo c f y' = evR Xo c f y)
    (hroot : ∃ N : ℕ, 0 < N ∧ ∀ y : FrPt Xo c (CAt σ), evR Xo c f y ^ N = 1)
    (c0 : ℂ) (hc0 : c0 ≠ 0) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)
    (hval : ∀ h γ : GA D V, MarkBy U V hr dict io F ik φ h γ → rdU U f (dict h).1 (dict h).2 =
      c0 * ((xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) : ℂ))
    (hxi : ∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V γ)) = 1)
    (s : Sim Dw) (hs : ∀ n, s.ν n = 1) (ρ : Xo.X ≅ Xo.X) (hρ : Xo.LevAut s ρ) :
    ∃ a : ℂ, ∀ y y' : FrPt Xo c (CAt σ), y'.x = y.x ≫ ρ.hom → toC (evR Xo c f y') = a * toC (evR Xo c f y) := by
  have hty := (GlobalTheory.Relab.relab_good _ H l c σ hσ).2.2.2 Dw g e
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have val : ∀ h : GA D V, ∃ k, ∃ γ ∈ GQ V,
      Marked V hr io l (U.X k).Λ (fun a => (φ k (F.t (ik k) a) : Fin r → D.host.E)) (γ * h) ∧
      ∀ (i : Fin F.n) P (y : FrPt Xo c (CAt σ)), i = ik k → IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P → y.x = F.u i P →
        toC (evR Xo c f y) = c0 * ((xi (Matrix.GeneralLinearGroup.det (finHom V h)) : ℂˣ) : ℂ) := by
    intro h
    obtain ⟨γ, hγ, hΛ, hm, -⟩ := hD.2 h
    refine ⟨(dict h).1, γ, hγ, ⟨hΛ, hm⟩, ?_⟩
    rintro _ P y rfl hP hy
    have hv := hval h γ ⟨hγ, hΛ, hm⟩
    rw [map_mul, map_mul, map_mul, hxi γ hγ, one_mul] at hv
    obtain ⟨hx, ex⟩ := rdU_eq U f _ _ (hv ▸ mul_ne_zero hc0 (Units.ne_zero _))
    obtain ⟨P₀, -, hP₀, hy₀, -⟩ := hD.1.2 (dict h).1 ⟨_, hx⟩
    rw [← hv, GlobalTheory.T.frameFree_finiteOrder_rule_const_periodSpace _ H Dw l Xo c σ f hf hfree hroot g _ F hty _ P P₀ y _ hP hP₀ hy hy₀, ex]
  have pt : ∀ y : FrPt Xo c (CAt σ), ∃ k P, IsPeriod (F.Di (ik k)) (fun j => relab c σ (e j).1) P ∧ y.x = F.u (ik k) P := by
    intro y
    obtain ⟨k, x, t, ht⟩ := hU.2.2.1 y
    obtain ⟨P, -, hP, hy, -⟩ := hD.1.2 k x
    exact ⟨k, P, hP, ht.1.trans hy⟩
  have hA' : ∀ {i i' : Fin F.n} (gam : (F.Di i).La ≃ₗ[𝓞 D.host.E] (F.Di i').La) a,
      ∃ x, gam (F.t i a) = F.t i' a + l.A • x := fun gam a =>
    ⟨gam (F.t _ a) - F.t _ a, by rw [hA, one_smul, add_sub_cancel]⟩
  obtain ⟨κ, hκ, hκ'⟩ := GlobalTheory.T.exists_adelic_unitary_of_lattice_isometries D V H Dw io hL hF s hs
  refine ⟨(xi (Matrix.GeneralLinearGroup.det (finHom V κ)) : ℂˣ), fun y y' hy => ?_⟩
  obtain ⟨k, P, hP, hyP⟩ := pt y
  obtain ⟨k', P', hP', hyP'⟩ := pt y'
  obtain ⟨h, hh⟩ := GlobalTheory.T.exists_adelic_element_of_marked_component_lattice D V H Dw l Xo _ g _ F hty r hr (U.X k) (ik k) (φ k) io (hW k) (hD.1.1 k) hL hF
  obtain ⟨k₁, γ₁, hγ₁, hm₁, hv₁⟩ := val h
  obtain ⟨k₂, γ₂, hγ₂, hm₂, hv₂⟩ := val (h * κ)
  obtain ⟨g₁, e₁, t₁⟩ := GlobalTheory.T.markedLattice_isometry_double_coset_move D V H Dw l r hr io (U.X k) (U.X k₁) _ _ (φ k) (φ k₁) (F.t _) (F.t _) LinearMap.id
    h γ₁ 1 (hW k) (hW k₁) (hD.1.1 k) (hD.1.1 k₁) hγ₁ rfl (fun a => ⟨0, zero_mem _, by
      rw [map_one, Units.val_one, Matrix.one_mulVec, smul_zero, add_zero]; rfl⟩) hh
    (by rw [mul_one]; exact hm₁)
  obtain ⟨g₂, e₂, t₂⟩ := GlobalTheory.T.markedLattice_isometry_double_coset_move D V H Dw l r hr io (U.X k) (U.X k₂) _ _ (φ k) (φ k₂) (F.t _) (F.t _) (s.f l.M)
    h γ₂ κ (hW k) (hW k₂) (hD.1.1 k) (hD.1.1 k₂) hγ₂ hκ (hκ' l.M hM) hh
    (by rw [mul_assoc]; exact hm₂)
  obtain ⟨g₃, e₃, t₃⟩ := GlobalTheory.LevStab.exists_isometry_of_levAut F hρ hP hP' (hyP ▸ hy.symm.trans hyP')
  have i₁ : ik k = ik k₁ := GlobalTheory.Dict.index_eq_of_marked_isometry F hpq hσ hty _ _ g₁ e₁ t₁ (hA' g₁)
  have i₂ : ik k' = ik k₂ := by
    refine GlobalTheory.Dict.index_eq_of_marked_isometry F hpq hσ hty _ _ (g₃.symm.trans g₂) (fun a b => ?_)
      (fun a ha => ?_) (hA' _)
    · rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, e₂, ← e₃, g₃.apply_symm_apply, g₃.apply_symm_apply]
    · obtain ⟨x, hx⟩ := t₂ a ha
      obtain ⟨z, hz⟩ := exists_eq_nsmul l (t₃ a) (sub_mem
        (GlobalTheory.LevStab.map_mem_smul_top _ g₃.toLinearMap (GlobalTheory.LevStab.map_mem_smul_top _ _
          (GlobalTheory.LevStab.map_mem_smul_top _ _ ha))) (GlobalTheory.LevStab.map_mem_smul_top _ _ ha))
      refine ⟨x - g₂ (g₃.symm z), ?_⟩
      have : F.t (ik k') a = g₃ (F.t (ik k) (s.f l.M a)) - l.M • z := by rw [← hz, sub_sub_cancel]
      rw [LinearEquiv.trans_apply, this, map_sub, map_sub, g₃.symm_apply_apply, hx, map_nsmul, map_nsmul, smul_sub,
        add_sub_assoc]
  rw [hv₁ _ P y i₁ hP hyP, hv₂ _ P' y' i₂ hP' hyP', map_mul, map_mul, map_mul, Units.val_mul]
  ring

attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem formPlus_of {D : D7} {Q : Par D} (hQ : Q.Pins) {j : ℕ} (hj : InR D j) {V : HSp D} (hV : V = D.sp.W j)
    {io : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hL : LatEmb V io) (hI : LatIsom V (Q.Dw j).EF io) :
    FormPlus V io := by
  subst hV
  obtain ⟨ε, hε⟩ := hI
  let ψ := (((D.sp.W j).frame.equivFun.symm.restrictScalars (𝓞 D.host.E)).toLinearMap) ∘ₗ io
  have hsp : Submodule.span D.host.E (Set.range ψ) = ⊤ := by
    have h1 : Set.range ψ = (D.sp.W j).frame.equivFun.symm.toLinearMap '' (latG (D.sp.W j) 1 : Set _) := by
      rw [← hL.2, LinearMap.coe_range, ← Set.range_comp]
      rfl
    rw [h1, Submodule.span_image, (GlobalTheory.RecDict.comp_latG D _).2.1, Submodule.map_top, LinearEquiv.range]
  have h1 := GlobalTheory.T.liftDatum_alternatingForm_sign_eq_one D Q.H (Q.Dw j) j hj hQ.1.2.1 hQ.1.2.2.1 (hQ.2.2.2 j hj).1 (hQ.2.2.2 j hj).2.1 ψ ε
    ((D.sp.W j).frame.equivFun.symm.injective.comp hL.1) hsp hε
  intro x y
  rw [hε, h1]
  simp

theorem rank_eq {D : D7} {Q : Par D} (hQ : Q.Pins) {j : ℕ} (hj : InR D j) : 1 ≤ (Q.Dw j).p + (Q.Dw j).q := by
  rw [(hQ.2.2.2 j hj).1, (hQ.2.2.2 j hj).2.1]
  have := hj.1; have := hj.2; have := D.R.m_add_three_le_k
  simp only [Ranks.sigW]; omega

theorem exists_root {D : D7} (T : Full D) (hT : LawsFull T) {j : ℕ} (hj : InR D j)
    (hxi : ∀ γ ∈ GQ (T.V j T.σ₀), T.xi (Matrix.GeneralLinearGroup.det (finHom (T.V j T.σ₀) γ)) = 1)
    {n : ℕ} (hn : D.R.r ≤ n) (s : Sim (T.Q.Dw j)) (hs : ∀ n, s.ν n = 1)
    (ρ : (T.dδ j n).Xo₂.X ≅ (T.dδ j n).Xo₂.X) (hρ : (T.dδ j n).Xo₂.LevAut s ρ) :
    ∃ u : 𝓞 T.Q.c.F, (u : T.Q.c.F) ≠ 0 ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (T.dδ j n).c₂.F K]
      (y y' : FrPt (T.dδ j n).Xo₂ (T.dδ j n).c₂ K), y'.x = y.x ≫ ρ.hom →
      evR _ _ (T.dδ j n).cδ y' = algebraMap (T.dδ j n).c₂.F K ((T.dδ j n).eF u) * evR _ _ (T.dδ j n).cδ y := by
  obtain ⟨hr, U, dict, c0, ⟨m, hm, hc0⟩, H⟩ := hT.xiVal j hj n
  obtain ⟨hU, hW, g, e, F, ik, φ, th, -, hD, hval⟩ := H ()
  obtain ⟨_, _, _, _, _, _, _, hL, hI, -⟩ := hT.j.adPin j hj T.σ₀ T.toCore.good_σ₀
  obtain ⟨_, ψ, _, -, -, hψ⟩ := hT.sh.dPhi j hj n hn
  obtain ⟨Cls, _, _, δ, gdet, hsec, hC⟩ := hT.sh.dRoot j hj n
  simp only [Bool.false_eq_true, if_false] at hC
  have hN : Nat.card Cls ≠ 0 := Nat.card_pos.ne'
  have hσ : T.σ₀.comp ((T.dδ j n).eF.symm : (T.dδ j n).c₂.F →+* T.Q.c.F) = (T.dδ j n).c₂.F.val.toRingHom :=
    RingHom.ext fun _ => rfl
  have hδ : ∀ z, δ z ^ Nat.card Cls = 1 := fun z => by rw [← map_pow, pow_card_eq_one', map_one]
  have key : ∀ σ, σ = (T.dδ j n).c₂.F.val.toRingHom → (GoodEmb (T.dδ j n).c₂ σ ∧
      ∃ N : ℕ, 0 < N ∧ ∀ y : FrPt (T.dδ j n).Xo₂ (T.dδ j n).c₂ (CAt σ), evR _ _ (T.dδ j n).cδ y ^ N = 1) ∧
      ∀ a : ℂ, (∀ y y' : FrPt (T.dδ j n).Xo₂ (T.dδ j n).c₂ (CAt σ), y'.x = y.x ≫ ρ.hom →
        toC (evR _ _ (T.dδ j n).cδ y') = a * toC (evR _ _ (T.dδ j n).cδ y)) →
      ∀ y y' : FrPt (T.dδ j n).Xo₂ (T.dδ j n).c₂ (CAt (T.dδ j n).c₂.F.val.toRingHom), y'.x = y.x ≫ ρ.hom →
        toC (evR _ _ (T.dδ j n).cδ y') = a * toC (evR _ _ (T.dδ j n).cδ y) := by
    rintro _ rfl
    refine ⟨⟨rfl, _, Nat.pos_of_ne_zero hN, fun y => ?_⟩, fun a h => h⟩
    rw [hC, ← map_pow, ← Units.val_pow_eq_pow_val, hδ, Units.val_one, map_one]
  obtain ⟨⟨hg, hroot⟩, htr⟩ := key _ hσ
  obtain ⟨a, ha⟩ := exists_ratio (T.V j T.σ₀) hr (U ()) (dict ()) _ e F ik φ th _ hg (hT.lvA j hj n)
    (rank_eq hT.p.pins hj) hU hW hD hL (formPlus_of hT.p.pins hj (hT.p.spaceW j hj _ T.toCore.good_σ₀) hL hI)
    _ hsec (fun K _ _ _ y y' h => GlobalTheory.ShortDescent.evR_eq_of_point_eq _ hψ y y' h) hroot c0
    (by rintro rfl; rw [zero_pow hm.ne'] at hc0; exact zero_ne_one hc0) T.xi hval hxi s hs ρ hρ
  replace ha := htr a ha
  have main : ∃ v : (T.dδ j n).c₂.Fˣ, v ^ Nat.card Cls = 1 ∧
      ∀ y y' : FrPt (T.dδ j n).Xo₂ (T.dδ j n).c₂ (CAt (T.dδ j n).c₂.F.val.toRingHom), y'.x = y.x ≫ ρ.hom →
        evR _ _ (T.dδ j n).cδ y' = algebraMap _ _ (v : (T.dδ j n).c₂.F) * evR _ _ (T.dδ j n).cδ y := by
    by_cases hex : ∃ y y' : FrPt (T.dδ j n).Xo₂ (T.dδ j n).c₂ (CAt (T.dδ j n).c₂.F.val.toRingHom),
        y'.x = y.x ≫ ρ.hom
    · obtain ⟨z, z', hz⟩ := hex
      refine ⟨δ (gdet z' * (gdet z)⁻¹), hδ _, fun y y' h => ?_⟩
      have h1 := ha z z' hz
      rw [hC, hC] at h1
      have h2 : (((δ (gdet z') : (T.dδ j n).c₂.Fˣ) : (T.dδ j n).c₂.F) : ℂ) =
        a * (((δ (gdet z) : (T.dδ j n).c₂.Fˣ) : (T.dδ j n).c₂.F) : ℂ) := h1
      have h3 : (((δ (gdet z' * (gdet z)⁻¹) : (T.dδ j n).c₂.Fˣ) : (T.dδ j n).c₂.F) : ℂ) = a := by
        have h4 : (((δ (gdet z) : (T.dδ j n).c₂.Fˣ) : (T.dδ j n).c₂.F) : ℂ) ≠ 0 := by
          exact_mod_cast (δ (gdet z)).ne_zero
        rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
        push_cast
        rw [h2, mul_inv_cancel_right₀ h4]
      exact (ha y y' h).trans (congrArg (· * _) h3.symm)
    · exact ⟨1, one_pow _, fun y y' h => absurd ⟨y, y', h⟩ hex⟩
  obtain ⟨v, hv, hmain⟩ := main
  have hint : IsIntegral ℤ ((T.dδ j n).eF.symm (v : (T.dδ j n).c₂.F)) := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hN) ?_
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hv, Units.val_one, map_one]
    exact isIntegral_one
  refine ⟨⟨_, hint⟩, ?_, fun K _ _ _ y y' h => ?_⟩
  · exact (map_ne_zero (T.dδ j n).eF.symm).2 v.ne_zero
  · obtain ⟨z, z', hz, -, hz'⟩ := GlobalTheory.Frames.exists_complex_framed_pair _ _ _ _ (T.dδ j n).Xo₂ (T.dδ j n).c₂ K y y'
    have := hz' _ hsec v (hmain z z' (hz _ h))
    exact this

end Adelic

end GlobalTheory.ShortMove

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.ShortMove

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem actLev_short : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Full D), LawsFull T → ∀ (j : ℕ) (hj : InR D j), (∀ γ₀ ∈ Formalism.L2.Theta.GQ (T.V j T.σ₀), T.xi (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.finHom (T.V j T.σ₀) γ₀)) = 1) → ∀ (w : WeightFamilies.Wt D j), D.R.r ≤ w.n → ∀ (γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l), ∀ f ∈ T.toTop.sh j w, ∃ (u : 𝓞 T.Q.c.F) (f' : T.R j), f' ∈ T.toTop.sh j w ∧ actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) γ f = (u : T.Q.c.F) • f' := by
  intro hC D T hT j hj hxi w hw γ f hf
  have hL := GlobalTheory.firstFiveLaws.1
  have hpq := rank_eq hT.p.pins hj
  have hA : T.Q.l.A = 1 := hT.p.pins.2.1.2
  have hAct := GlobalTheory.T.actLev_full_level_group_framedPoints D T.Q j hpq hA
  have hLev := hT.sh.dLev j hj w.n
  have hA₂ := hT.lvA j hj w.n
  obtain ⟨inst, hnab⟩ := hT.sh.dNab j hj w.n
  obtain ⟨ph, ψ, x₀, -, hpin, htie⟩ := hT.sh.dPhi j hj w.n hw
  have hTot := hT.sh.shTot j hj (wtA w) w.n (dom_wtA w)
  obtain ⟨g, hν, hγ, hg⟩ := GlobalTheory.T.exists_completed_isometry_inducing_half_level_automorphism _ _ (T.Q.Dw j) T.Q.l γ
  obtain ⟨ρ₂, hρ₂⟩ := GlobalTheory.LevelActionLaws.exists_levAut hpq (T.dδ j w.n).Xo₂ g (by rw [hν, sub_self]; exact dvd_zero _)
  obtain ⟨u, hu, hcd⟩ := exists_root T hT hj hxi hw g hν ρ₂ hρ₂
  obtain ⟨hsec, Λ, N, x0, P, hU, hb, hb₂, hO, hX, hP, hR⟩ := hf
  unfold Top.sh
  generalize T.dδ j w.n = d at *
  have hM := hLev.2.1
  have hM₁ : 0 < T.Q.l.M := by have := T.Q.l.three_le; omega
  have hpd : 0 < d.pd := Nat.pos_of_mul_pos_left (hM ▸ (by have := d.l₂.three_le; omega : 0 < d.l₂.M))
  have hI : ∀ a, g.f d.l₂.M a - a ∈ d.I • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La) := fun a => by
    have hpI : ((d.pd : ℕ) : 𝓞 D.host.E) ∈ d.I := by
      refine (Ideal.mul_le_inf.trans inf_le_left : d.I * d.I.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ d.I) ?_
      rw [GlobalTheory.DatumInverseCharacter.half_prod hM hLev.2.2.2.1]
      exact Ideal.mem_span_singleton_self _
    have h1 := GlobalTheory.DatumInverseCharacter.mem_of_modN _ hpI (g.tower d.pd T.Q.l.M hpd hM₁ a)
    have h2 := GlobalTheory.DatumInverseCharacter.mem_of_modN _ hpI (hg d.pd hpd hLev.2.2.1 a)
    have := add_mem h1 h2
    rwa [sub_add_sub_cancel, mul_comm, ← hM] at this
  have hγ' : ∀ a, g.f d.l₂.M a - liftLa γ a ∈ T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La) := fun a => by
    have hMb : ((T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ T.Q.l.Mb := by
      refine (Ideal.mul_le_inf.trans inf_le_left :
        T.Q.l.Mb * T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ T.Q.l.Mb) ?_
      rw [T.Q.l.prod]
      exact Ideal.mem_span_singleton_self _
    have h1 := GlobalTheory.DatumInverseCharacter.mem_of_modN _ hMb (g.tower T.Q.l.M d.pd hM₁ hpd a)
    have h2 : g.f T.Q.l.M a - liftLa γ a ∈ T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La) :=
      (Submodule.Quotient.eq _).1 ((hγ a).trans (liftLa_spec γ a).symm)
    have := add_mem h1 h2
    rwa [sub_add_sub_cancel, ← hM] at this
  obtain ⟨σq, hσ, hdat⟩ := GlobalTheory.T.levelCoverDatum_similitude_adjoint_transport _ _ _ _ _ _ _ d hM hLev.2.2.2.1 ph ψ x₀ hpin g hI
  obtain ⟨x0', hX', hw'⟩ := hdat _ x0 hX
  obtain ⟨hρs, ν₂, hη, hηA⟩ := hρ₂
  have hmv₂ : IsLevMove ρ₂.hom ν₂ (g.f d.l₂.M) (g.f d.l₂.A) := ⟨hρs, hη, hηA⟩
  have hP₂ := (GlobalTheory.admissible_columns_le_and_harmonic_map_cover _ _ _ _ _ _ _ d).2 _ P hP.1
  refine ⟨u, (u : T.Q.c.F)⁻¹ • actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) γ f,
    ⟨Submodule.smul_mem _ _ (actL_mem _ _ _ _ hAct.total hAct.nat hAct.bor _ γ hsec),
      Λ, N, x0', P, hU, hb, hb₂, hO, hX', hP, ?_⟩, (smul_inv_smul₀ hu _).symm⟩
  intro k _ _ _ _ hk y y₂ ho
  have hev := evalAt_actL hAct (hT.p.evalWD j hj) frMap_trans_id γ hsec.1 y
  obtain ⟨ρ, ν, -, hmv, hfr⟩ := mvPt_spec hAct.total γ y
  generalize mvPt _ _ γ y = y' at hev hfr
  obtain ⟨y₂', hfr₂⟩ := (GlobalTheory.exists_unique_frMove _ _ _ _ d.Xo₂ d.c₂ ρ₂.hom ν₂ hρs k y₂).1
  obtain ⟨r', m', hr', hm', hE'⟩ := GlobalTheory.T.exists_conj_levelMap_by_levelMoves _ _ _ _ _ _ _ d hLev.2.2.2.2.2.1 ρ ν ρ₂ ν₂ _ _ _ _ hmv hmv₂ hγ'
    (fun a => ⟨_, by rw [hA, one_smul]⟩)
  have ho' := GlobalTheory.T.liesOverFramed_of_square_levelMoves _ _ _ _ _ _ _ d ρ ν ρ₂.hom ν₂ r' m' hr' hm' k y y' y₂ y₂' ho hfr hfr₂
  obtain ⟨z₂, hz₂⟩ := hLev.2.2.2.2.2.2.1 k hk y'
  obtain ⟨v, hv, hfv⟩ := hR k hk y' z₂ hz₂
  obtain ⟨v', hv', -⟩ := (hTot Λ N x0 P hU hb hb₂ hO hX hP).1 k y₂'
  have e₁ := GlobalTheory.ShortLiftInvariance.cover_product_indep_of_lift hL hC _ _ _ _ _ _ _ d
    (GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.2 _ _ _ hpq).1 hLev (hA₂.trans hA.symm) hnab ⟨ph, ψ, x₀, hpin, htie⟩ Λ N hU hb₂ hO _ _ hP₂ x0 _
    r' m' hE' k hk y' z₂ y₂' hz₂ ho' v v' hv hv'
  have e₂ := GlobalTheory.T.shortThetaValue_under_levelMove hL hC _ _ _ _ d.Xo₂ d.c₂ d.nab₂ hnab k ρ₂.hom ν₂ _ _ y₂ y₂' hmv₂ hfr₂ σq hσ
    _ _ _ hP₂ (d.w x0) Λ _ N v' hv'
  rw [funext hw'] at e₂
  refine ⟨v', e₂, (evalAt_smul _ _ _ _ y).trans ?_⟩
  refine (congrArg (_ * ·) (hev.trans (hfv.trans e₁))).trans ?_
  rw [hcd k y₂ y₂' hfr₂.1, hk, ← mul_assoc, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hu, map_one, one_mul]

end GlobalTheory.ShortMove
end
end
