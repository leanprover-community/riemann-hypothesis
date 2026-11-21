import Mathlib
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.RootOnFund
import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedAtlasSncSection
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsClosedSectionBoundaryStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryPointsClosed
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmHostRankBoundsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsArithVarOfSncModel
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerBoundHeightOnBoundary
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsFrames
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsGram
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalPairSumGramBound
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsLocal
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsBounds
import BuildAid.ForwardExisting
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsBlockpos
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsPeriod
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsImmersion
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsHom

section
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB.BMx.Frames

theorem exists_finite_good_frames : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j n : ℕ) (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n), ∃ (q : ℕ) (O : Fin q → Set Rb.X) (F : Fin q → FrameData ι Ψ N M.Ω M.blk), (∀ l, IsOpen (O l)) ∧ (∀ x, ∃ l, x ∈ O l) ∧ (∀ l, M.IsFrame (F l)) ∧ ∀ l, ∀ x ∈ closure (O l), M.GoodAt (F l) (mCoordIdeal (Rb.lift x x)) := by
  exact @PositivityTheory.Xgp.t_c_bm_exists_frames

end GlobalTheory.CompanionTheory.Ar.PB.BMx.Frames
end

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_frame_cover : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j n : ℕ) (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n), ∃ (q : ℕ) (O : Fin q → Set Rb.X) (F : Fin q → FrameData ι Ψ N M.Ω M.blk), (∀ l, IsOpen (O l)) ∧ (∀ x, ∃ l, x ∈ O l) ∧ (∀ l, M.IsFrame (F l)) ∧ ∀ l, ∀ x ∈ closure (O l), M.GoodAt (F l) (mCoordIdeal (Rb.lift x x)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.BMx.Frames.exists_finite_good_frames
end

section
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.flagModel_frame_height_comparison : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), ∀ (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), M.IsFrame F → ∀ (τ : CMType H) (w : (Σ k, baseIdx ι M.blk k) → ℂ) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z w → 𝔐.Interior z → M.GoodAt F (mCoordIdeal w) → 𝔐.M.GramAt 𝔐.t.PP.L z (gb tie F τ) (HodgeMetric.gramFn 𝔐 (gb tie F τ) w) ∧ (HodgeMetric.gramFn 𝔐 (gb tie F τ) w).PosDef ∧ ∀ a b, tie.omFrame F τ a (dualFam tie F τ b) = if a = b then 1 else 0 := by
  first | exact @PositivityTheory.Xgp.t_c_bm_exists_gram | exact PositivityTheory.Xgp.t_c_bm_exists_gram
end

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagModel_frame_height_comparison : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), ∀ (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), M.IsFrame F → ∀ (τ : CMType H) (w : (Σ k, baseIdx ι M.blk k) → ℂ) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z w → 𝔐.Interior z → M.GoodAt F (mCoordIdeal w) → 𝔐.M.GramAt 𝔐.t.PP.L z (gb tie F τ) (HodgeMetric.gramFn 𝔐 (gb tie F τ) w) ∧ (HodgeMetric.gramFn 𝔐 (gb tie F τ) w).PosDef ∧ ∀ a b, tie.omFrame F τ a (dualFam tie F τ b) = if a = b then 1 else 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.flagModel_frame_height_comparison
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open GlobalTheory.CompanionTheory.Ar.FramePeriods
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.BMx

theorem exists_isFramePeriods_noGlobal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), ∀ (a b : CMType H ⊕ CMType H) (N : ℕ) (bb : Fin N → ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) (n : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (χ : SncChart (mCoordIdeal y) n Bd) (t₀ : Fin n → ℂ) (cc : (k : K) → J k) (f : Ω), (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w → (w ∈ Bd ↔ ¬ 𝔐.Interior z)) → t₀ ∈ Metric.ball (0 : Fin n → ℂ) 1 → (∀ p : Cpt 𝔐.ξ, InChart 𝔐.ξ (segreCoord y) cc p → unitAt 𝔐.ξ p f → (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb p) → InFrameDomain y cc f (χ.γ t₀) → ∃ (a₀ g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (L : Flat.LogPeriods n a₀ g Λ) (π : Equiv.Perm (Fin n)) (ρ : ℝ) (U : Fin N → (Fin n → ℂ) → Fin g → ℂ), HodgeMetric.IsFramePeriods 𝔐 (fun k => ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) χ t₀ cc f L π ρ U := by
  intro E _ _ _ H D Xo l c Y S Ω _ _ K _ J _ y 𝔐 a b N bb n Bd χ t₀ cc f hBd ht₀ hfr hdom
  classical
  obtain ⟨a₀, π, ρ₀, ha, hρ₀, hρ₀', hπ, hgeo⟩ := GlobalTheory.T.snc_chart_local_normal_form K J Ω y _ n Bd χ t₀ cc f ht₀ hdom
  have hw : DifferentiableOn ℂ (fun u => χ.γ (HodgeMetric.recentre t₀ ρ₀ π u)) (Metric.ball 0 1) := by
    refine χ.analytic.differentiableOn.comp ?_ fun u hu => (hgeo ρ₀ hρ₀ le_rfl u hu).1
    unfold HodgeMetric.recentre
    exact (differentiable_const _ |>.add (differentiable_pi.2 fun i => by
      simpa using (differentiable_apply (π i) : Differentiable ℂ fun u : Fin n → ℂ => u (π i)).const_mul (ρ₀ : ℂ))).differentiableOn
  set w : (Fin n → ℂ) → (Σ k, J k) → ℂ := fun u => χ.γ (HodgeMetric.recentre t₀ ρ₀ π u) with hwdef
  have htie := 𝔐.tie
  have hall := 𝔐.all
  have hex : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, ∃ z : Sp ℂ ⟶ 𝔐.X, genPt 𝔐.ξ ⤳ centre z ∧ CoordsAt 𝔐.ξ y z (w u) := fun u hu =>
    (GlobalTheory.T.complex_points_iff_centres 𝔐.X Ω 𝔐.ξ K J y htie (w u)).1 (χ.mem _ (hgeo ρ₀ hρ₀ le_rfl u hu).1)
  haveI : Nonempty (Sp ℂ ⟶ 𝔐.X) := ⟨(hex 0 (by simp)).choose⟩
  choose! p hp₀ hp using hex
  have huniq : ∀ (z z' : Sp ℂ ⟶ 𝔐.X) (w' : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w' → CoordsAt 𝔐.ξ y z' w' → z = z' := fun z z' w' h h' => by
    obtain ⟨e1, -, e3⟩ := GlobalTheory.T.local_ring_points_existsUnique 𝔐.X Ω 𝔐.ξ K J y htie ℂ
    exact (e1 w' h.1 (e3 z w' (hall _) h).1).unique ⟨hall _, h⟩ ⟨hall _, h'⟩

  have fin : ∀ (g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (L : Flat.LogPeriods n a₀ g Λ) (ρ₁ : ℝ)
      (U : Fin N → (Fin n → ℂ) → Fin g → ℂ), 0 < ρ₁ → ρ₁ ≤ 1 →
      (∀ k, DifferentiableOn ℂ (U k) (Metric.ball 0 1)) → LinearIndependent ℂ (fun k => U k 0) →
      (∀ u ∈ Flat.punct n a₀ 1, ∀ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (w ((ρ₁ : ℂ) • u)) →
        𝔐.M.GramAt 𝔐.t.PP.L z (fun k => ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) (HodgeMetric.periodGram L U u)) →
      ∃ (a₀ g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (L : Flat.LogPeriods n a₀ g Λ) (π : Equiv.Perm (Fin n)) (ρ : ℝ) (U : Fin N → (Fin n → ℂ) → Fin g → ℂ), HodgeMetric.IsFramePeriods 𝔐 (fun k => ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) χ t₀ cc f L π ρ U := by
    intro g Λ _ L ρ₁ U h1 h2 h3 h4 h5
    have hle : ρ₀ * ρ₁ ≤ ρ₀ := by nlinarith
    have hpos : 0 < ρ₀ * ρ₁ := mul_pos hρ₀ h1
    refine ⟨a₀, g, Λ, inferInstance, L, π, ρ₀ * ρ₁, U, hpos, by nlinarith, h3, h4, hπ, fun u hu => ?_⟩
    obtain ⟨g1, g2, g3⟩ := hgeo _ hpos hle u hu
    refine ⟨g1, g2, g3, fun hup z hz => ?_⟩
    rw [recentre_mul] at hz
    exact h5 u hup z hz
  have hb0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := by simp
  have hfr0 : (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb ⟨centre (p 0), hall _⟩ := by
    have hd := (hgeo ρ₀ hρ₀ le_rfl 0 hb0).2.1
    obtain ⟨c1, c2⟩ := GlobalTheory.T.frame_domain_in_segre_chart 𝔐.X Ω 𝔐.ξ K J y htie (p 0) (w 0) cc f (hall _) (hp 0 hb0) hd
    exact hfr _ c1 c2
  by_cases hpq : D.p + D.q = 0
  · have hV : ∀ s, 𝔐.Vgen s = ⊥ := fun s => by
      obtain ⟨-, -, b', hb', -⟩ := 𝔐.vb s ⟨genPt 𝔐.ξ, specializes_rfl⟩ trivial
      have hr : labelRk D s = 0 := by
        rcases s with s | s <;> simp only [labelRk, Sum.elim_inl, Sum.elim_inr] <;> omega
      have : IsEmpty (Fin (labelRk D s)) := by rw [hr]; infer_instance
      have e : Set.range b' = ∅ := Set.range_eq_empty b'
      rw [e, Submodule.span_empty] at hb'
      exact hb'.symm
    have hli := hfr0.1
    haveI : Subsingleton ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b) := by
      rw [hV a, hV b, sup_bot_eq]
      infer_instance
    haveI : IsEmpty (Fin N) := ⟨fun k => hli.ne_zero k (Subsingleton.elim _ _)⟩
    obtain ⟨Λ, _, ⟨L⟩⟩ := zeroPeriods n a₀ ha
    exact fin 0 Λ _ L 1 (fun _ _ => 0) one_pos le_rfl (fun k => isEmptyElim k) linearIndependent_empty_type
      fun u _ z _ => ⟨fun k => isEmptyElim k, fun k => isEmptyElim k, fun k => isEmptyElim k⟩
  have hpq' : 1 ≤ D.p + D.q := Nat.one_le_iff_ne_zero.2 hpq
  have hhol : IsHolTo (Metric.ball 0 1) p := GlobalTheory.T.holomorphic_coords_of_generic_point 𝔐.X Ω 𝔐.ξ K J y htie hall n _ w p Metric.isOpen_ball hw hp
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := ⟨⟩
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.holomorphic_disc_over_number_field_ring c.F 𝔐.X (𝔐.f ≫ Y.s) n p hhol
  have hint : ∀ u ∈ Flat.punct n a₀ 1, 𝔐.Interior (p u) := fun u hu => by
    have h1 := (hgeo ρ₀ hρ₀ le_rfl u hu.1).2.2
    have h2 := hBd (p u) (w u) (hp u hu.1)
    by_contra h
    exact (h1.2 hu) (h2.2 h)
  set σ : KA l →+* ℂ := τ.comp (IntermediateField.inclusion c.le).toRingHom with hσ
  have hsq : (σ (baseKA l).ρ) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, (baseKA l).ρ_sq, H.sqrt_neg_disc_sq]
    simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with hs | hs
  · obtain ⟨g, Λ, _, L, ρ₁, U, h1, h2, h3, h4, h5⟩ := core 𝔐 a b N bb n a₀ p τ hpq' hs ha hhol hτ hint (hall _) hfr0
    refine fin g Λ _ L ρ₁ U h1 h2 h3 h4 fun u hu z hz => ?_
    rw [huniq z _ _ hz (hp _ (smul_mem_ball' h1 h2 hu.1))]
    exact h5 u hu
  · have hcc : (spMap (starRingEnd ℂ) : Sp ℂ ⟶ Sp ℂ) ≫ spMap (starRingEnd ℂ) = 𝟙 _ := by
      refine (Spec.map_comp (CommRingCat.ofHom (starRingEnd ℂ)) (CommRingCat.ofHom (starRingEnd ℂ))).symm.trans ?_
      convert Spec.map_id (CommRingCat.of ℂ)
      ext x
      simp
    set p' : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X) := fun u => spMap (starRingEnd ℂ) ≫ p (star u) with hp'
    have hcoord : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, CoordsAt 𝔐.ξ y (p' u) (fun q => star (w (star u) q)) := fun u hu =>
      (GlobalTheory.T.conjugate_point_same_centre 𝔐.X Ω 𝔐.ξ K J y _ _).2 (hp _ (star_mem_ball' hu))
    have hcen : ∀ u, centre (p' u) = centre (p (star u)) := fun u => (GlobalTheory.T.conjugate_point_same_centre 𝔐.X Ω 𝔐.ξ K J y _ (w 0)).1
    have hhol' : IsHolTo (Metric.ball 0 1) p' := GlobalTheory.T.holomorphic_coords_of_generic_point 𝔐.X Ω 𝔐.ξ K J y htie hall n _ _ p' Metric.isOpen_ball
      (diffOn_star' hw) hcoord
    have hτ' : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, p' u ≫ 𝔐.f ≫ Y.s =
        spMap (((starRingEnd ℂ).comp τ).comp (algebraMap (𝓞 c.F) c.F)) := fun u hu => by
      rw [hp', Category.assoc, hτ _ (star_mem_ball' hu)]
      exact (Spec.map_comp (CommRingCat.ofHom (τ.comp (algebraMap (𝓞 c.F) c.F))) (CommRingCat.ofHom (starRingEnd ℂ))).symm
    have hint' : ∀ u ∈ Flat.punct n a₀ 1, 𝔐.Interior (p' u) := fun u hu => by
      change centre (p' u) ∈ _
      rw [hcen]
      exact hint _ (star_mem_punct' hu)
    have hs' : (((starRingEnd ℂ).comp τ).comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0 := by
      change (starRingEnd ℂ) (σ (baseKA l).ρ) = H.rt0
      rw [hs, map_neg, rt0_conj_neg_ne_zero, neg_neg]
    have hfr0' : (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb ⟨centre (p' 0), hall _⟩ := by
      have e : (⟨centre (p' 0), hall _⟩ : Cpt 𝔐.ξ) = ⟨centre (p 0), hall _⟩ := Subtype.ext (by
        show centre (p' 0) = centre (p 0)
        rw [hcen, star_zero])
      rw [e]
      exact hfr0
    obtain ⟨g, Λ, _, L', ρ₁, U', h1, h2, h3, h4, h5⟩ := core 𝔐 a b N bb n a₀ p' _ hpq' hs' ha hhol' hτ' hint' (hall _) hfr0'
    obtain ⟨L, hL⟩ := GlobalTheory.T.exists_conjugate_log_periods n a₀ g N Λ L' U' (GlobalTheory.T.bijective_logPeriods_T n a₀ g Λ L')
    refine fin g Λ _ L ρ₁ (fun k u' => star (U' k (star u'))) h1 h2 (fun k => diffOn_star' (h3 k)) ?_ fun u hu z hz => ?_
    · refine Fintype.linearIndependent_iff.2 fun c' hc' k => ?_
      have e := congrArg star hc'
      simp only [star_sum, star_smul, star_star, star_zero] at e
      have := Fintype.linearIndependent_iff.1 h4 (fun k => star (c' k)) (by simpa [star_smul] using e) k
      simpa using this
    · rw [hL u hu, huniq z _ _ hz (hp _ (smul_mem_ball' h1 h2 hu.1))]
      have := GlobalTheory.T.gramAt_conj_point_map_conj E H D l (Xo l) c Y S Ω K J y 𝔐 _ N _ _ (h5 (star u) (star_mem_punct' hu))
      have e : spMap (starRingEnd ℂ) ≫ p' ((ρ₁ : ℂ) • star u) = p ((ρ₁ : ℂ) • u) := by
        rw [hp']
        simp only
        rw [← Category.assoc, hcc, Category.id_comp, star_smul, star_star]
        simp
      rwa [e] at this

end GlobalTheory.CompanionTheory.Ar.PB.BMx
end
end

section
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
open PositivityTheory.Xgp.c_bm_exists_local GroundTheory.Heights₂.Heights.LowerBoundFree in

theorem GlobalTheory.CompanionTheory.Ar.PB.BMx.exists_gram_logBounds_noGlobal : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), ∀ (n : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (L : LocPot Rb.X) (s : Rb.X → Rb.X → ℂ) (Bat : FinHolAtlas n Rb.X), IsPotential Rb.A L → IsSection Rb.A L s → (∀ p, logNormSec L s p ≤ 0) → IsAdaptedAtlas Rb.A Bat L s → (∀ (x : Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (Rb.lift x x) → (x ∉ bdry s ↔ 𝔐.Interior z)) → ∀ (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), M.IsFrame F → ∀ (τ : CMType H) (k : Fin Bat.n) (w₀ : Fin n → ℂ), w₀ ∈ Metric.closedBall (0 : Fin n → ℂ) (3 / 2) → M.GoodAt F (mCoordIdeal (Rb.lift ((Bat.chart k).symm w₀) ((Bat.chart k).symm w₀))) → ∃ ε c C : ℝ, 0 < ε ∧ 0 < c ∧ 0 < C ∧ ∀ w : Fin n → ℂ, ‖w - w₀‖ < ε → (Bat.chart k).symm w ∉ bdry s → (baseGram tie F τ Rb ((Bat.chart k).symm w)).PosDef ∧ ((baseGram tie F τ Rb ((Bat.chart k).symm w))⁻¹ - (c : ℂ) • (1 : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ)).PosSemidef ∧ (((C * rW L s ((Bat.chart k).symm w) : ℝ) : ℂ) • (1 : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ) - (baseGram tie F τ Rb ((Bat.chart k).symm w))⁻¹).PosSemidef ∧ ∀ a b, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => baseGram tie F τ Rb ((Bat.chart k).symm w') a b) w ∧ ‖fderiv ℝ (fun w' => baseGram tie F τ Rb ((Bat.chart k).symm w') a b) w‖ ≤ C * Real.exp (rW L s ((Bat.chart k).symm w) / 2) := by
  intro _ E _ _ _ H D Xo l c Y S K _ ι _ Φ _ y M 𝔐 tie n Rb L s Bat _ _ hnorm hAd hInt F hF τ k w₀ hw₀ hgood
  classical
  obtain ⟨hAB, hball, -, M₀, hM⟩ := hAd
  obtain ⟨S₀, m, hm, hS, hr⟩ := hM k
  have tp := GlobalTheory.T.local_ring_points_existsUnique 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie ℂ
  have uniq : ∀ {z z' : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} {w}, CoordsAt 𝔐.ξ M.x z w → CoordsAt 𝔐.ξ M.x z' w → z = z' :=
    fun {z z' w} h h' => (tp.1 w h.1 (tp.2.2 z w (𝔐.all _) h).1).unique ⟨𝔐.all _, h⟩ ⟨𝔐.all _, h'⟩
  have orb : ∀ {z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} {w w'}, CoordsAt 𝔐.ξ M.x z w → SameOrbit w' w →
      CoordsAt 𝔐.ξ M.x z w' := fun {z w w'} h ⟨a, ha, e⟩ =>
    ((tp.2.2 z w (𝔐.all _) h).2 _).2 ⟨fun k => Units.mk0 (a k) (ha k), e⟩
  have pts : ∀ w ∈ mcPts (mCoordIdeal M.x), ∃ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, CoordsAt 𝔐.ξ M.x z w := fun w hw => by
    obtain ⟨z, -, hz⟩ := (GlobalTheory.T.complex_points_iff_centres 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie w).1 hw
    exact ⟨z, hz⟩
  have gfn : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w Γ, CoordsAt 𝔐.ξ M.x z w → 𝔐.Interior z →
      𝔐.M.GramAt 𝔐.t.PP.L z (gb tie F τ) Γ → HodgeMetric.gramFn 𝔐 (gb tie F τ) w = Γ := by
    intro z w Γ hw hi hΓ
    have hex : ∃ (Γ : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X),
        CoordsAt 𝔐.ξ M.x z w ∧ 𝔐.Interior z ∧ 𝔐.M.GramAt 𝔐.t.PP.L z (gb tie F τ) Γ := ⟨Γ, z, hw, hi, hΓ⟩
    unfold HodgeMetric.gramFn
    rw [dif_pos hex]
    obtain ⟨z₀, hw₀, hi₀, hΓ₀⟩ := hex.choose_spec
    rw [uniq hw₀ hw] at hΓ₀
    exact GlobalTheory.T.gram_matrix_change_frame E H D l (Xo l) c Y S M.Ω _ _ M.x 𝔐 z _ _ _ _
      (GlobalTheory.T.interior_point_polarised E H D l (Xo l) c Y S M.Ω _ _ M.x 𝔐 z hi) hΓ₀ hΓ
  let Bd : Set ((Σ k, baseIdx ι M.blk k) → ℂ) :=
    {w | ∀ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, CoordsAt 𝔐.ξ M.x z w → ¬ 𝔐.Interior z}
  have hBd : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ M.x z w → (w ∈ Bd ↔ ¬ 𝔐.Interior z) :=
    fun z w hz => ⟨fun h => h z hz, fun h z' hz' => uniq hz hz' ▸ h⟩
  have hZ : ∀ x₀, ∀ x ∈ Rb.U x₀, Rb.lift x₀ x ∈ Bd ↔ x ∈ bdry s := by
    intro x₀ x hx
    obtain ⟨z, hz⟩ := pts _ (Rb.mem x₀ x hx)
    rw [hBd z _ hz, ← hInt x z (orb hz (Rb.compat x x₀ x ⟨Rb.mem_U x, hx⟩)), not_not]
  have hw₀' : ‖w₀‖ ≤ 3 / 2 := mem_closedBall_zero_iff.1 hw₀
  have hw₀t : w₀ ∈ (Bat.chart k).target := hball k (mem_closedBall_zero_iff.2 (by linarith))
  obtain ⟨ρ, π, χ, hρ, hρ', hU, hγ, ha⟩ := exists_sncChart Rb Bat hAB k w₀ hw₀t Bd (bdry s) S₀ hS hZ
  have hγ0 : χ.γ 0 = Rb.lift ((Bat.chart k).symm w₀) ((Bat.chart k).symm w₀) := by
    rw [hγ, HodgeMetric.recentre_zero]
  obtain ⟨z₀, hz₀⟩ := pts _ (Rb.mem _ _ (Rb.mem_U ((Bat.chart k).symm w₀)))
  obtain ⟨f, hf, hfg⟩ := exists_goodDomain M F 𝔐.tie (𝔐.all _) hz₀ hgood
  obtain ⟨a₀, g, Λ, _, LP, π', ρ', U, hP⟩ := exists_isFramePeriods_noGlobal E H D Xo l c Y S M.Ω _ _ M.x 𝔐 (.inl τ) (.inr τ) _
    (gbS tie F τ) n Bd χ 0 F.c f hBd (Metric.mem_ball_self one_pos)
    (fun p h1 h2 => PositivityTheory.Xgp.isFrameAt_comap_gbS E H D Xo l c Y S K ι Φ y M 𝔐 tie F hF τ p (hfg p h1 h2))
    (hγ0 ▸ hf)
  obtain ⟨ε, c₀, C, hε, hερ, hc₀, hC, hb⟩ := GlobalTheory.T.period_gram_comparison_bound n a₀ g _ χ.a Λ LP U 0 π' ρ' hP.1 hP.2.1 hP.2.2.1
    hP.2.2.2.1 hP.2.2.2.2.1
  obtain ⟨A, hA⟩ := exists_hasFDerivAt_uncentre w₀ ρ π
  have hcu : Continuous (HodgeMetric.uncentre w₀ ρ π) := (HodgeMetric.contDiff_uncentre w₀ ρ π).continuous
  have hcu' : Continuous (HodgeMetric.uncentre 0 ρ' π') := (HodgeMetric.contDiff_uncentre 0 ρ' π').continuous

  have pg : ∀ w ∈ Metric.ball w₀ ρ, HodgeMetric.uncentre 0 ρ' π' (HodgeMetric.uncentre w₀ ρ π w) ∈ Flat.punct n a₀ 1 →
      baseGram tie F τ Rb ((Bat.chart k).symm w) =
        HodgeMetric.periodGram LP U (HodgeMetric.uncentre 0 ρ' π' (HodgeMetric.uncentre w₀ ρ π w)) := by
    intro w hw hu
    obtain ⟨hb1, -, hbd, hg⟩ := hP.2.2.2.2.2 _ hu.1
    rw [HodgeMetric.recentre_uncentre 0 hP.1, hγ, HodgeMetric.recentre_uncentre w₀ hρ] at hbd hg
    obtain ⟨z, hz⟩ := pts _ (Rb.mem _ _ (hU w hw).2)
    have hi : 𝔐.Interior z := by_contra fun h => hbd.2 hu ((hBd z _ hz).2 h)
    exact gfn z _ _ (orb hz (Rb.compat _ _ _ ⟨Rb.mem_U _, (hU w hw).2⟩)) hi (hg hu z hz)
  have h0 : ∀ᶠ w in nhds w₀, ‖HodgeMetric.uncentre w₀ ρ π w - 0‖ < ε := by
    have : ContinuousAt (fun w => ‖HodgeMetric.uncentre w₀ ρ π w - 0‖) w₀ := by fun_prop
    refine this.eventually_lt continuousAt_const ?_
    simpa [HodgeMetric.uncentre_self] using hε
  obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.eventually_nhds_iff_ball.1 h0
  refine ⟨min ε₁ ρ, c₀, C * (1 + |M₀|) + C * Real.exp (|M₀| / 2) * ‖A‖, lt_min hε₁ hρ, hc₀, by positivity,
    fun w hw hwb => ?_⟩
  have hwρ : ‖w - w₀‖ < ρ := hw.trans_le (min_le_right _ _)
  have hwB : w ∈ Metric.ball w₀ ρ := mem_ball_iff_norm.2 hwρ
  have ht := hb₁ w (mem_ball_iff_norm.2 (hw.trans_le (min_le_left _ _)))
  have ht1 := HodgeMetric.uncentre_mem_ball hρ π hwρ
  have hub := HodgeMetric.uncentre_mem_ball hP.1 π' (ht.trans_le hερ)
  have hu : HodgeMetric.uncentre 0 ρ' π' (HodgeMetric.uncentre w₀ ρ π w) ∈ Flat.punct n a₀ 1 := by
    have hcl := (hP.2.2.2.2.2 _ hub).2.2.1
    rw [HodgeMetric.recentre_uncentre 0 hP.1, hγ, HodgeMetric.recentre_uncentre w₀ hρ, hZ _ _ (hU w hwB).2] at hcl
    exact hcl.1 hwb
  obtain ⟨b1, b2, b3⟩ := hb _ ht (mem_ball_zero_iff.1 ht1) hu
  have hev : ∀ᶠ w' in nhds w, baseGram tie F τ Rb ((Bat.chart k).symm w') =
      HodgeMetric.periodGram LP U (HodgeMetric.uncentre 0 ρ' π' (HodgeMetric.uncentre w₀ ρ π w')) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hwB,
      (hcu'.comp hcu).continuousAt.eventually ((HodgeMetric.isOpen_punct n a₀ 1).mem_nhds hu)] with w' h1 h2
    exact pg w' h1 h2
  have hw2 : ‖w‖ ≤ 2 := by
    have := norm_add_le (w - w₀) w₀
    rw [sub_add_cancel] at this
    linarith
  have hlog := logR_le hρ (by linarith) hm hw2
    (fun i hi h => hwb ((hS w (hU w hwB).1).2 ⟨i, hi, h⟩)) ha
  have hrM := abs_le.1 ((hr w (mem_closedBall_zero_iff.2 hw2) hwb).trans (le_abs_self M₀))
  have hre : 1 ≤ rW L s ((Bat.chart k).symm w) := by
    have := hnorm ((Bat.chart k).symm w)
    have h2 := Real.add_one_le_exp (1 : ℝ)
    unfold rW
    linarith
  generalize (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < χ.a then
    Real.log (1 / ‖HodgeMetric.uncentre w₀ ρ π w i‖ ^ 2) else 0) = R at b2 b3 hlog
  generalize rW L s ((Bat.chart k).symm w) = r at hrM hre ⊢
  have hR : R ≤ r + |M₀| := by linarith [hrM.1]
  have hM0 := abs_nonneg M₀
  have hX : 0 ≤ C * Real.exp (|M₀| / 2) * ‖A‖ := by positivity
  rw [hev.self_of_nhds]
  refine ⟨posDef_of_inv hc₀ b1, b1, psd_mono ?_ b2, fun a b => ?_⟩
  · have h1 : R ≤ (1 + |M₀|) * r := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 hC.le
    nlinarith
  · have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t => HodgeMetric.periodGram LP U (HodgeMetric.uncentre 0 ρ' π' t) a b) (HodgeMetric.uncentre w₀ ρ π w) :=
      (GlobalTheory.T.period_gram_smooth_punctured n a₀ g _ Λ LP U hP.2.2.1 a b _ hu).comp _ (HodgeMetric.contDiff_uncentre 0 ρ' π').contDiffAt
    have h2 : (fun w' => baseGram tie F τ Rb ((Bat.chart k).symm w') a b) =ᶠ[nhds w]
        (fun t => HodgeMetric.periodGram LP U (HodgeMetric.uncentre 0 ρ' π' t) a b) ∘ HodgeMetric.uncentre w₀ ρ π := by
      filter_upwards [hev] with w' hw'
      rw [hw']
      rfl
    refine ⟨(h1.comp w (HodgeMetric.contDiff_uncentre w₀ ρ π).contDiffAt).congr_of_eventuallyEq h2, ?_⟩
    rw [h2.fderiv_eq, fderiv_comp w (h1.differentiableAt (by simp)) (hA w).differentiableAt, (hA w).fderiv]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h3 : Real.exp (R / 2) ≤ Real.exp (|M₀| / 2) * Real.exp (r / 2) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    have h4 := (b3 a b).trans (mul_le_mul_of_nonneg_left h3 hC.le)
    have h5 := mul_le_mul_of_nonneg_right h4 (norm_nonneg A)
    have h6 : 0 ≤ C * (1 + |M₀|) * Real.exp (r / 2) := by positivity
    nlinarith
end

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagModel_global_height_identity : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), ∀ (n : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (L : LocPot Rb.X) (s : Rb.X → Rb.X → ℂ) (Bat : FinHolAtlas n Rb.X), IsPotential Rb.A L → IsSection Rb.A L s → (∀ p, logNormSec L s p ≤ 0) → IsAdaptedAtlas Rb.A Bat L s → (∀ (x : Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (Rb.lift x x) → (x ∉ bdry s ↔ 𝔐.Interior z)) → ∀ (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), M.IsFrame F → ∀ (τ : CMType H) (k : Fin Bat.n) (w₀ : Fin n → ℂ), w₀ ∈ Metric.closedBall (0 : Fin n → ℂ) (3 / 2) → M.GoodAt F (mCoordIdeal (Rb.lift ((Bat.chart k).symm w₀) ((Bat.chart k).symm w₀))) → ∃ ε c C : ℝ, 0 < ε ∧ 0 < c ∧ 0 < C ∧ ∀ w : Fin n → ℂ, ‖w - w₀‖ < ε → (Bat.chart k).symm w ∉ bdry s → (baseGram tie F τ Rb ((Bat.chart k).symm w)).PosDef ∧ ((baseGram tie F τ Rb ((Bat.chart k).symm w))⁻¹ - (c : ℂ) • (1 : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ)).PosSemidef ∧ (((C * rW L s ((Bat.chart k).symm w) : ℝ) : ℂ) • (1 : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ) - (baseGram tie F τ Rb ((Bat.chart k).symm w))⁻¹).PosSemidef ∧ ∀ a b, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => baseGram tie F τ Rb ((Bat.chart k).symm w') a b) w ∧ ‖fderiv ℝ (fun w' => baseGram tie F τ Rb ((Bat.chart k).symm w') a b) w‖ ≤ C * Real.exp (rW L s ((Bat.chart k).symm w) / 2) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.BMx.exists_gram_logBounds_noGlobal
end

section
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

theorem GlobalTheory.CompanionTheory.Metric.blockG_bounds_of_local_gram_bounds : ∀ (n p q : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A B : FinHolAtlas n X) (Z Cl U : Set X) (r : X → ℝ) (Γ : X → Matrix (Fin (p + q)) (Fin (p + q)) ℂ), A.Compatible B → (∀ k, Metric.closedBall (0 : Fin n → ℂ) 2 ⊆ (B.chart k).target) → (∀ x, ∃ k, x ∈ (B.chart k).source ∧ B.chart k x ∈ Metric.ball (0 : Fin n → ℂ) 1) → IsClosed Z → IsClosed Cl → IsOpen U → U ⊆ Cl → (∀ x, x ∉ Z → Real.exp 1 ≤ r x) → (∀ (k : Fin B.n) (w₀ : Fin n → ℂ), w₀ ∈ Metric.closedBall (0 : Fin n → ℂ) (3 / 2) → (B.chart k).symm w₀ ∈ Cl → ∃ ε c C : ℝ, 0 < ε ∧ 0 < c ∧ 0 < C ∧ ∀ w : Fin n → ℂ, ‖w - w₀‖ < ε → (B.chart k).symm w ∉ Z → (Γ ((B.chart k).symm w)).PosDef ∧ ((Γ ((B.chart k).symm w))⁻¹ - (c : ℂ) • (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ)).PosSemidef ∧ (((C * r ((B.chart k).symm w) : ℝ) : ℂ) • (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) - (Γ ((B.chart k).symm w))⁻¹).PosSemidef ∧ ∀ a b, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => Γ ((B.chart k).symm w') a b) w ∧ ‖fderiv ℝ (fun w' => Γ ((B.chart k).symm w') a b) w‖ ≤ C * Real.exp (r ((B.chart k).symm w) / 2)) → (∀ a b, A.SmoothOn (U \ Z) (fun x => (blockG (Γ x) a b).re) ∧ A.SmoothOn (U \ Z) (fun x => (blockG (Γ x) a b).im)) ∧ ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → (∀ x ∈ Cl \ Z, (((r x ^ C : ℝ) : ℂ) • (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) - blockG (Γ x)).PosSemidef ∧ (((r x ^ C : ℝ) : ℂ) • blockG (Γ x) - 1).PosSemidef) ∧ ∀ (a b : Fin (p + q)) (k : Fin B.n), ∀ w ∈ Metric.ball (0 : Fin n → ℂ) (3 / 2), (B.chart k).symm w ∈ Cl \ Z → ‖fderiv ℝ (fun w' => blockG (Γ ((B.chart k).symm w')) a b) w‖ ≤ C * r ((B.chart k).symm w) ^ C * Real.exp (r ((B.chart k).symm w) / 2) :=
  @PositivityTheory.Xgp.t_c_bm_exists_bounds
end

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cutoff_function_on_compatible_atlas : ∀ (n p q : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A B : FinHolAtlas n X) (Z Cl U : Set X) (r : X → ℝ) (Γ : X → Matrix (Fin (p + q)) (Fin (p + q)) ℂ), A.Compatible B → (∀ k, Metric.closedBall (0 : Fin n → ℂ) 2 ⊆ (B.chart k).target) → (∀ x, ∃ k, x ∈ (B.chart k).source ∧ B.chart k x ∈ Metric.ball (0 : Fin n → ℂ) 1) → IsClosed Z → IsClosed Cl → IsOpen U → U ⊆ Cl → (∀ x, x ∉ Z → Real.exp 1 ≤ r x) → (∀ (k : Fin B.n) (w₀ : Fin n → ℂ), w₀ ∈ Metric.closedBall (0 : Fin n → ℂ) (3 / 2) → (B.chart k).symm w₀ ∈ Cl → ∃ ε c C : ℝ, 0 < ε ∧ 0 < c ∧ 0 < C ∧ ∀ w : Fin n → ℂ, ‖w - w₀‖ < ε → (B.chart k).symm w ∉ Z → (Γ ((B.chart k).symm w)).PosDef ∧ ((Γ ((B.chart k).symm w))⁻¹ - (c : ℂ) • (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ)).PosSemidef ∧ (((C * r ((B.chart k).symm w) : ℝ) : ℂ) • (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) - (Γ ((B.chart k).symm w))⁻¹).PosSemidef ∧ ∀ a b, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => Γ ((B.chart k).symm w') a b) w ∧ ‖fderiv ℝ (fun w' => Γ ((B.chart k).symm w') a b) w‖ ≤ C * Real.exp (r ((B.chart k).symm w) / 2)) → (∀ a b, A.SmoothOn (U \ Z) (fun x => (blockG (Γ x) a b).re) ∧ A.SmoothOn (U \ Z) (fun x => (blockG (Γ x) a b).im)) ∧ ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → (∀ x ∈ Cl \ Z, (((r x ^ C : ℝ) : ℂ) • (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) - blockG (Γ x)).PosSemidef ∧ (((r x ^ C : ℝ) : ℂ) • blockG (Γ x) - 1).PosSemidef) ∧ ∀ (a b : Fin (p + q)) (k : Fin B.n), ∀ w ∈ Metric.ball (0 : Fin n → ℂ) (3 / 2), (B.chart k).symm w ∈ Cl \ Z → ‖fderiv ℝ (fun w' => blockG (Γ ((B.chart k).symm w')) a b) w‖ ≤ C * r ((B.chart k).symm w) ^ C * Real.exp (r ((B.chart k).symm w) / 2) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Metric.blockG_bounds_of_local_gram_bounds
end

section
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB.BMx

theorem blockG_isBlockDiag_posDef :
    ∀ (p q : ℕ) (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ), Γ.PosDef →
      IsBlockDiag p (blockG Γ) ∧ (blockG Γ).PosDef :=
  PositivityTheory.Xgp.t_c_bm_exists_blockpos

end GlobalTheory.CompanionTheory.Ar.PB.BMx
end

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockG_blockDiag_posDef : ∀ (p q : ℕ) (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ), Γ.PosDef → IsBlockDiag p (blockG Γ) ∧ (blockG Γ).PosDef := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.BMx.blockG_isBlockDiag_posDef
end

section
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_local_holo_isPeriodGram_blockG_baseGram : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), 1 ≤ D.p → 1 ≤ D.q → ∀ (n : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (s : Rb.X → Rb.X → ℂ), (∀ (x : Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (Rb.lift x x) → (x ∉ bdry s ↔ 𝔐.Interior z)) → IsClosed (bdry s) → ∀ (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), M.IsFrame F → ∀ (τ : CMType H) (x : Rb.X), x ∉ bdry s → M.GoodAt F (mCoordIdeal (Rb.lift x x)) → ∃ (V : Set Rb.X) (P : Rb.X → Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ), IsOpen V ∧ x ∈ V ∧ (∀ a b, Rb.A.HoloOn V fun x' => P x' a b) ∧ ∀ x' ∈ V, IsPeriodGram D.p (P x') (blockG (baseGram tie F τ Rb x')) := by
  first | exact @PositivityTheory.Xgp.t_c_bm_exists_period | exact PositivityTheory.Xgp.t_c_bm_exists_period
end

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_holo_isPeriodGram_blockG_baseGram : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), 1 ≤ D.p → 1 ≤ D.q → ∀ (n : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (s : Rb.X → Rb.X → ℂ), (∀ (x : Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (Rb.lift x x) → (x ∉ bdry s ↔ 𝔐.Interior z)) → IsClosed (bdry s) → ∀ (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), M.IsFrame F → ∀ (τ : CMType H) (x : Rb.X), x ∉ bdry s → M.GoodAt F (mCoordIdeal (Rb.lift x x)) → ∃ (V : Set Rb.X) (P : Rb.X → Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ), IsOpen V ∧ x ∈ V ∧ (∀ a b, Rb.A.HoloOn V fun x' => P x' a b) ∧ ∀ x' ∈ V, IsPeriodGram D.p (P x') (blockG (baseGram tie F τ Rb x')) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.exists_local_holo_isPeriodGram_blockG_baseGram
end

section
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.flagModel_height_lower_estimate : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), 1 ≤ D.p → 1 ≤ D.q → ∀ (d : ℕ), 𝔐.IsCover d → ∀ (Rb : AnLogRes (mCoordIdeal M.x) ⊤ (Fintype.card (CMType H) * D.p * D.q)) (s : Rb.X → Rb.X → ℂ), (∀ (x : Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (Rb.lift x x) → (x ∉ bdry s ↔ 𝔐.Interior z)) → IsClosed (bdry s) → ∀ (q : ℕ) (O : Fin q → Set Rb.X) (F : Fin q → FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), (∀ l, IsOpen (O l)) → (∀ x, ∃ l, x ∈ O l) → (∀ l, M.IsFrame (F l)) → (∀ l, ∀ x ∈ O l, M.GoodAt (F l) (mCoordIdeal (Rb.lift x x))) → ∃ l, ∃ x ∈ O l \ bdry s, ∃ (V : Set Rb.X) (Pi : CMType H → Rb.X → Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ), x ∈ V ∧ IsPeriodOn Rb.A D.p V Pi (fun τ x' => blockG (baseGram tie (F l) τ Rb x')) ∧ ∀ k, x ∈ (Rb.A.chart k).source → ∀ v : Fin (Fintype.card (CMType H) * D.p * D.q) → ℂ, (∀ τ (a b : Fin (D.p + D.q)), D.p + D.q - D.p ≤ (a : ℕ) → (b : ℕ) < D.p + D.q - D.p → ((Pi τ x)⁻¹ * Matrix.of fun a b => fderiv ℂ (fun w => Pi τ ((Rb.A.chart k).symm w) a b) (Rb.A.chart k x) v) a b = 0) → v = 0 := by
  first | exact @PositivityTheory.Xgp.t_c_bm_exists_immersion | exact PositivityTheory.Xgp.t_c_bm_exists_immersion
end

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagModel_height_lower_estimate : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), 1 ≤ D.p → 1 ≤ D.q → ∀ (d : ℕ), 𝔐.IsCover d → ∀ (Rb : AnLogRes (mCoordIdeal M.x) ⊤ (Fintype.card (CMType H) * D.p * D.q)) (s : Rb.X → Rb.X → ℂ), (∀ (x : Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (Rb.lift x x) → (x ∉ bdry s ↔ 𝔐.Interior z)) → IsClosed (bdry s) → ∀ (q : ℕ) (O : Fin q → Set Rb.X) (F : Fin q → FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), (∀ l, IsOpen (O l)) → (∀ x, ∃ l, x ∈ O l) → (∀ l, M.IsFrame (F l)) → (∀ l, ∀ x ∈ O l, M.GoodAt (F l) (mCoordIdeal (Rb.lift x x))) → ∃ l, ∃ x ∈ O l \ bdry s, ∃ (V : Set Rb.X) (Pi : CMType H → Rb.X → Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ), x ∈ V ∧ IsPeriodOn Rb.A D.p V Pi (fun τ x' => blockG (baseGram tie (F l) τ Rb x')) ∧ ∀ k, x ∈ (Rb.A.chart k).source → ∀ v : Fin (Fintype.card (CMType H) * D.p * D.q) → ℂ, (∀ τ (a b : Fin (D.p + D.q)), D.p + D.q - D.p ≤ (a : ℕ) → (b : ℕ) < D.p + D.q - D.p → ((Pi τ x)⁻¹ * Matrix.of fun a b => fderiv ℂ (fun w => Pi τ ((Rb.A.chart k).symm w) a b) (Rb.A.chart k x) v) a b = 0) → v = 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.flagModel_height_lower_estimate
end

section
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.flagModel_resolution_integrability : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), ∀ (n : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (s : Rb.X → Rb.X → ℂ), (∀ (x : Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (Rb.lift x x) → (x ∉ bdry s ↔ 𝔐.Interior z)) → ∀ (q : ℕ) (O : Fin q → Set Rb.X) (F : Fin q → FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), (∀ x, ∃ l, x ∈ O l) → (∀ l, M.IsFrame (F l)) → (∀ l, ∀ x ∈ O l, M.GoodAt (F l) (mCoordIdeal (Rb.lift x x))) → ∃ hom : CMType H × Fin (D.p + D.q) → HermLine ι, (∀ p, (hom p).a = M.dy p) ∧ (∀ l, ∀ x ∈ O l \ bdry s, ∀ p, M.IsInducedAt (F l) (Rb.lift x x) p (blockG (baseGram tie (F l) p.1 Rb x)) (hom p)) ∧ ∀ p, ∀ z ∈ mcPts (mCoordIdeal y), ∀ x, x ∉ bdry s → SameOrbit (basePart M.blk z) (Rb.lift x x) → (hom p).h (fun q => starRingEnd ℂ (z q)) = (hom p).h z := by
  first | exact @PositivityTheory.Xgp.t_c_bm_exists_hom | exact PositivityTheory.Xgp.t_c_bm_exists_hom
end

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagModel_resolution_integrability : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), ∀ (n : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (s : Rb.X → Rb.X → ℂ), (∀ (x : Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (Rb.lift x x) → (x ∉ bdry s ↔ 𝔐.Interior z)) → ∀ (q : ℕ) (O : Fin q → Set Rb.X) (F : Fin q → FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), (∀ x, ∃ l, x ∈ O l) → (∀ l, M.IsFrame (F l)) → (∀ l, ∀ x ∈ O l, M.GoodAt (F l) (mCoordIdeal (Rb.lift x x))) → ∃ hom : CMType H × Fin (D.p + D.q) → HermLine ι, (∀ p, (hom p).a = M.dy p) ∧ (∀ l, ∀ x ∈ O l \ bdry s, ∀ p, M.IsInducedAt (F l) (Rb.lift x x) p (blockG (baseGram tie (F l) p.1 Rb x)) (hom p)) ∧ ∀ p, ∀ z ∈ mcPts (mCoordIdeal y), ∀ x, x ∉ bdry s → SameOrbit (basePart M.blk z) (Rb.lift x x) → (hom p).h (fun q => starRingEnd ℂ (z q)) = (hom p).h z := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.flagModel_resolution_integrability
end

section
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.BMx

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

theorem card_cmType_pos : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), 0 < Fintype.card (CMType H) := by
  intro E _ _ _ H
  have h := (GlobalTheory.T.cm_host_rank_bounds E H).2.2
  have h2 : 0 < Module.finrank ℚ E := Module.finrank_pos
  by_contra h0
  have h3 : Fintype.card (CMType H) = 0 := by omega
  simp_all

theorem exists_coordsAt_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (n : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (x : Rb.X), ∃ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, CoordsAt 𝔐.ξ M.x z (Rb.lift x x) := by
  intro E _ _ _ H D Xo l c Y S K _ ι _ Φ _ y M 𝔐 n Rb x
  obtain ⟨z, -, hz⟩ := (GlobalTheory.T.complex_points_iff_centres 𝔐.X M.Ω 𝔐.ξ (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.x 𝔐.tie _).1 (Rb.mem x x (Rb.mem_U x))
  exact ⟨z, hz⟩

theorem mem_bdry_conj_iff : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] (x₀ : (Σ k, J k) → Ω) (n : ℕ) (bd : Ideal (MRing J)) (Rb : AnLogRes (mCoordIdeal x₀) ⊤ n) (s : Rb.X → Rb.X → ℂ), (∀ p, p ∈ bdry s ↔ Rb.lift p p ∈ mcPts bd) → (∀ z ∈ mcPts (mCoordIdeal x₀) ∩ mcPts bd, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul c z ∈ mcPts (mCoordIdeal x₀) ∩ mcPts bd) → (∀ z ∈ mcPts (mCoordIdeal x₀) ∩ mcPts bd, GroundTheory.Heights₂.Heights.LowerBoundFree.conjVec z ∈ mcPts (mCoordIdeal x₀) ∩ mcPts bd) → ∀ p p', SameOrbit (Rb.lift p' p') (fun q => starRingEnd ℂ (Rb.lift p p q)) → (p' ∈ bdry s ↔ p ∈ bdry s) := by
  intro K _ J _ Ω _ x₀ n bd Rb s hb htor hconj p p' ho
  obtain ⟨c, hc, e⟩ := ho
  have hm : ∀ p, Rb.lift p p ∈ mcPts (mCoordIdeal x₀) := fun p => Rb.mem p p (Rb.mem_U p)
  rw [hb p', hb p]
  constructor
  · intro h
    have h1 := hconj _ ⟨hm p', h⟩
    have h2 := htor _ h1 (fun k => (starRingEnd ℂ (c k))⁻¹) (fun k => inv_ne_zero ((map_ne_zero _).2 (hc k)))
    have e2 : GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul (fun k => (starRingEnd ℂ (c k))⁻¹)
        (GroundTheory.Heights₂.Heights.LowerBoundFree.conjVec (Rb.lift p' p')) = Rb.lift p p := by
      funext q
      simp only [GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul, GroundTheory.Heights₂.Heights.LowerBoundFree.conjVec]
      rw [e]
      simp [inv_mul_cancel_left₀, (map_ne_zero (starRingEnd ℂ)).2 (hc q.1)]
    rw [e2] at h2
    exact h2.2
  · intro h
    have h1 := hconj _ ⟨hm p, h⟩
    have h2 := htor _ h1 c hc
    have e2 : GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul c
        (GroundTheory.Heights₂.Heights.LowerBoundFree.conjVec (Rb.lift p p)) = Rb.lift p' p' := by
      funext q
      simp only [GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul, GroundTheory.Heights₂.Heights.LowerBoundFree.conjVec]
      rw [e]
    rw [e2] at h2
    exact h2.2

theorem gramAt_sub {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {Li : Type} [AddCommGroup Li] [Module Ω Li] {M : LieModel G ξ Li} {L : LB G.left}
    {z : Spec (CommRingCat.of ℂ) ⟶ X} {r r' : ℕ} {b : Fin r → Li} {Γ : Matrix (Fin r) (Fin r) ℂ}
    (h : M.GramAt L z b Γ) (e : Fin r' → Fin r) : M.GramAt L z (fun i => b (e i)) (Γ.submatrix e e) := by
  obtain ⟨v, hv, h'⟩ := h
  exact ⟨fun i => v (e i), fun i => hv _, fun p q => h' _ _⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {M : FlagModel y (CMType H) (D.p + D.q) D.p} {𝔐 : HodgeCpt Y S M.x}

theorem gb_wEmb (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H) (a : Fin D.p) :
    gb tie F τ (wEmb D.p D.q a) = tie.wFrame F τ a := by
  simp only [gb, gbS, ← blockEquiv_inr, Equiv.symm_apply_apply, Sum.elim_inr]

theorem gb_omEmb (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H) (a : Fin D.q) :
    gb tie F τ (omEmb D.p D.q a) = (dualFam tie F τ a : 𝔐.Li) := by
  simp only [gb, gbS, ← blockEquiv_inl, Equiv.symm_apply_apply, Sum.elim_inl]

theorem gramAt_wFrame (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H)
    {z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} {Γ : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ}
    (h : 𝔐.M.GramAt 𝔐.t.PP.L z (gb tie F τ) Γ) :
    𝔐.M.GramAt 𝔐.t.PP.L z (tie.wFrame F τ) (wBlock (blockG Γ)) := by
  rw [wBlock_blockG]
  have := gramAt_sub h (wEmb D.p D.q)
  simp only [gb_wEmb] at this
  exact this

theorem dualGramAt_omFrame (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H)
    {z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} {Γ : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ}
    (h : 𝔐.M.GramAt 𝔐.t.PP.L z (gb tie F τ) Γ) (hp : Γ.PosDef)
    (hd : ∀ a b, tie.omFrame F τ a (dualFam tie F τ b) = if a = b then 1 else 0) :
    DualGramAt 𝔐.M 𝔐.t.PP.L z (𝔐.Vgen (.inr τ)) (tie.omFrame F τ) (omBlock (blockG Γ)) := by
  refine ⟨dualFam tie F τ, omBlock Γ, hd, ?_, ?_⟩
  · have := gramAt_sub h (omEmb D.p D.q)
    simp only [gb_omEmb] at this
    exact this
  · have hpos : (omBlock Γ).PosDef := hp.submatrix (omEmb_strictMono D.p D.q).injective
    have hu : IsUnit (omBlock Γ).det := (Matrix.isUnit_iff_isUnit_det _).1 hpos.isUnit
    rw [omBlock_blockG, Matrix.transpose_nonsing_inv, Matrix.transpose_transpose]
    exact Matrix.nonsing_inv_mul _ hu

theorem baseMetricExists_of_given : Given → PB.BaseMetricExists := by
  intro hG E _ _ _ H D l Xo₀ c Y S K _ ι _ Φ _ y M 𝔐 tie d hp hq hcov hsnc
  classical
  obtain ⟨Xo, rfl⟩ : ∃ Xo : ∀ l' : Level H, Moduli D l', Xo l = Xo₀ :=
    ⟨Function.update (fun l' => (hG.1.2.1 E H D l' (by omega)).some) l Xo₀, Function.update_self ..⟩
  classical
  set n := Fintype.card (CMType H) * D.p * D.q with hn
  have hn1 : 1 ≤ n := by
    have : 0 < Fintype.card (CMType H) := card_cmType_pos E H
    exact Nat.mul_pos (Nat.mul_pos this hp) hq
  obtain ⟨bd, hbd, hint⟩ := hsnc
  have harith := GlobalTheory.T.isArithVar_of_snc_model 𝔐.X M.Ω 𝔐.ξ (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.x n bd hn1 𝔐.tie hbd
  obtain ⟨hcl, htor, hconj⟩ := GlobalTheory.T.boundary_points_closed 𝔐.X M.Ω 𝔐.ξ (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.x
    (abLocus 𝔐.t.G) bd 𝔐.tie hint
  obtain ⟨Rb, L, s, nb, m, W, potL, sec, snc, norm_le, hbdry, hrconj⟩ :=
    GlobalTheory.T.lowerBound_height_on_boundary (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.Ω M.x n bd hbd harith hcl htor hconj
  obtain ⟨Bat, adapted⟩ := GlobalTheory.T.adapted_atlas_snc_section Rb.A L s m W potL sec snc norm_le
  have hInt : ∀ (x : Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (Rb.lift x x) →
      (x ∉ bdry s ↔ 𝔐.Interior z) := fun x z hz => by
    rw [hbdry x, hint z _ hz, not_not]
  have hZ : IsClosed (bdry s) := GlobalTheory.T.isClosed_section_boundary n Rb.X Rb.A L s sec
  obtain ⟨q, O, F, hO, hOc, hF, hgood⟩ :=
    GlobalTheory.T.exists_finite_frame_cover K ι Φ y (CMType H) (D.p + D.q) D.p n M Rb
  have hgood' : ∀ l, ∀ x ∈ O l, M.GoodAt (F l) (mCoordIdeal (Rb.lift x x)) :=
    fun l x hx => hgood l x (subset_closure hx)
  have hr : ∀ x, x ∉ bdry s → Real.exp 1 ≤ rW L s x := fun x _ => by
    have := norm_le x
    unfold rW
    linarith
  have hb := fun (i : Fin q) (τ : CMType H) => GlobalTheory.T.cutoff_function_on_compatible_atlas n D.p D.q Rb.X Rb.A Bat (bdry s) (closure (O i)) (O i) (rW L s)
    (baseGram tie (F i) τ Rb) adapted.1 adapted.2.1 adapted.2.2.1 hZ isClosed_closure (hO i) subset_closure hr
    (fun k w₀ hw₀ hc => GlobalTheory.T.flagModel_global_height_identity hG E H D Xo l c Y S K ι Φ y M 𝔐 tie n Rb L s Bat potL sec norm_le adapted hInt (F i)
      (hF i) τ k w₀ hw₀ (hgood i _ hc))
  choose C₀ hC₀ using fun i τ => (hb i τ).2
  obtain ⟨Cst, hCst⟩ : ∃ Cst : ℝ, ∀ i τ, C₀ i τ ≤ Cst := by
    refine ⟨∑ i, ∑ τ, |C₀ i τ|, fun i τ => ?_⟩
    calc C₀ i τ ≤ |C₀ i τ| := le_abs_self _
      _ ≤ ∑ τ, |C₀ i τ| := Finset.single_le_sum (f := fun τ => |C₀ i τ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)
      _ ≤ ∑ i, ∑ τ, |C₀ i τ| := Finset.single_le_sum (f := fun i => ∑ τ, |C₀ i τ|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hcoords : ∀ x : Rb.X, ∃ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, CoordsAt 𝔐.ξ M.x z (Rb.lift x x) := exists_coordsAt_lift E H D Xo l c Y S K ι Φ y M 𝔐 n Rb
  have hgr := fun (i : Fin q) (τ : CMType H) (x : Rb.X) (hx : x ∈ O i \ bdry s) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X)
      (hz : CoordsAt 𝔐.ξ M.x z (Rb.lift x x)) =>
    GlobalTheory.T.flagModel_frame_height_comparison E H D Xo l c Y S K ι Φ y M 𝔐 tie (F i) (hF i) τ (Rb.lift x x) z hz ((hInt x z hz).1 hx.2) (hgood' i x hx.1)
  obtain ⟨hom, hdeg, hind, hconjH⟩ := GlobalTheory.T.flagModel_resolution_integrability E H D Xo l c Y S K ι Φ y M 𝔐 tie n Rb s hInt q O F hOc hF hgood'
  have hper : ∀ i, ∀ x ∈ O i \ bdry s, ∃ V Pi, x ∈ V ∧
      IsPeriodOn Rb.A D.p V Pi (fun τ x' => blockG (baseGram tie (F i) τ Rb x')) := by
    intro i x hx
    have := fun τ => GlobalTheory.T.exists_local_holo_isPeriodGram_blockG_baseGram hG E H D Xo l c Y S K ι Φ y M 𝔐 tie hp hq n Rb s hInt hZ (F i) (hF i) τ x hx.2 (hgood' i x hx.1)
    choose V P hV hxV hP hPG using this
    refine ⟨⋂ τ, V τ, P, Set.mem_iInter.2 hxV, isOpen_iInter_of_finite hV, fun τ a b => ?_, fun τ x' hx' => hPG τ x' (Set.mem_iInter.1 hx' τ)⟩
    intro k
    exact (hP τ a b k).mono (Set.inter_subset_inter_right _ (Set.preimage_mono (Set.iInter_subset _ τ)))
  obtain ⟨lI, xI, hxI, VI, PiI, hxV, hPer, himm⟩ := GlobalTheory.T.flagModel_height_lower_estimate hG E H D Xo l c Y S K ι Φ y M 𝔐 tie hp hq d hcov Rb s hInt hZ q O F hO hOc hF hgood'
  refine ⟨{ Rb := Rb, L := L, s := s, nb := nb, m := m, W := W, potL := potL, sec := sec, snc := snc, norm_le := norm_le,
            Bat := Bat, adapted := adapted, q := q, O := O, O_open := hO, O_cover := hOc, F := F, isFrame := hF, good := hgood'
            G := fun i τ x => blockG (baseGram tie (F i) τ Rb x)
            G_pos := ?_, G_smooth := fun i τ a b => (hb i τ).1 a b
            Cst := Cst
            size := fun i τ x hx => ((hC₀ i τ Cst (hCst i τ)).1 x ⟨subset_closure hx.1, hx.2⟩)
            grad := fun i τ a b k w hw hx => (hC₀ i τ Cst (hCst i τ)).2 a b k w hw ⟨subset_closure hx.1, hx.2⟩
            period := hper
            immersion := ⟨lI, xI, hxI, VI, PiI, hxV, hPer, himm⟩
            hom := hom, hom_deg := hdeg, induced := hind }, ?_, ?_⟩
  · intro i τ x hx
    obtain ⟨z, hz⟩ := hcoords x
    exact GlobalTheory.T.blockG_blockDiag_posDef D.p D.q _ (hgr i τ x hx z hz).2.1
  · refine ⟨hInt, fun i τ x hx z hz => ?_, fun i τ x hx z hz => ?_⟩
    · exact gramAt_wFrame tie (F i) τ (hgr i τ x hx z hz).1
    · exact dualGramAt_omFrame tie (F i) τ (hgr i τ x hx z hz).1 (hgr i τ x hx z hz).2.1 (hgr i τ x hx z hz).2.2
  · refine ⟨fun x x' ho => ?_, fun p z hz x hx ho => hconjH p z hz x hx ho⟩
    exact ⟨mem_bdry_conj_iff (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.Ω M.x n bd Rb s hbdry htor hconj x x' ho, hrconj x x' ho⟩

end GlobalTheory.CompanionTheory.Ar.PB.BMx
end
end

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_metric_exists_of_given : Given → PB.BaseMetricExists := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.BMx.baseMetricExists_of_given
end
