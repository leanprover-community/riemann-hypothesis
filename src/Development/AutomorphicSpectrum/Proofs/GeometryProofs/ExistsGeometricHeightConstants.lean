import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineHeightInvariantScalingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HeightOfZeroDimVariety
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspIntersectionComparison
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ComponentHeightLowerBound
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspIntersectionHeight
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricHeightBound
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieSignatureNumberFieldStatement
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.IntegralPointExtendsCompact
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.HeightComparisonGlobalModel
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Rt0ConjNegNeZero
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightDominatesEventually
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmHostRankBounds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CuspWeightIntegrableOnFundamentalSet
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
import Development.WeilBound.CoreStatements.VolumeEquality.SheetPiecesExistence
import Development.WeilBound.CoreStatements.VolumeEquality.SheetPiecesComponent
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeMiddle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionDegreeLower

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.cusp_intersection_finite : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (U : ((Σ k, J k) → ℂ) → ℝ) (M : XModel Dc) (S' : BoundedRegularisationSetting M Dc.Xo Hd.aMu (corrW Hd U)) (z : Sp ℂ ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ) (x : ℝ), Or.𝔐.IsCuspWeight Or.sm U → CoordsAt Or.𝔐.ξ Dc.y z w → Or.PhiWeight z w x → x ≤ S'.B.ph (M.proj w) + Real.log (S'.ref.h w) := by
  intro hG E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or U M S' z w x hU hz hx
  have hw : w ∈ mcPts (mCoordIdeal Dc.y) :=
    (GlobalTheory.T.complex_points_iff_centres _ Ω Or.𝔐.ξ K J Dc.y Or.𝔐.tie w).2 ⟨z, Or.𝔐.all _, hz⟩
  haveI := LevelTowerAlt.Xo_dense Dc hw
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨δ, hδ, h⟩ := GlobalTheory.T.cusp_intersection_comparison hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or U z w x hU hz hx (ε / 3) (by linarith)
  have hsub : Dc.Xo ⊆ mcPts (mCoordIdeal Dc.y) := fun _ h => h.1
  have h1 : ∀ᶠ w' in 𝓝[Dc.Xo] w, S'.B.ph (M.proj w') < S'.B.ph (M.proj w) + ε / 3 :=
    ((M.cont w hw).mono hsub).tendsto.eventually (LevelTowerAlt.ph_usc S'.B _ _ (by linarith))
  have hc : ContinuousWithinAt (fun w' => Real.log (S'.ref.h w')) Dc.Xo w :=
    ((S'.ref_smooth.continuousOn w hw.1).mono fun _ h => h.1.1).log (S'.ref.pos w hw.1).ne'
  have h2 : ∀ᶠ w' in 𝓝[Dc.Xo] w, Real.log (S'.ref.h w') < Real.log (S'.ref.h w) + ε / 3 :=
    hc.tendsto.eventually (gt_mem_nhds (by linarith))
  have h3 : ∀ᶠ w' in 𝓝[Dc.Xo] w, ‖w' - w‖ < δ := by
    refine mem_nhdsWithin_of_mem_nhds ?_
    filter_upwards [Metric.ball_mem_nhds w hδ] with w' hw'
    rwa [Metric.mem_ball, dist_eq_norm] at hw'
  obtain ⟨w', a, b, c', d⟩ := (h1.and (h2.and (h3.and self_mem_nhdsWithin))).exists
  have e1 := h w' d c'
  have e2 := S'.ph_eq w' ⟨d, d.1⟩
  linarith
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_intersection_finite : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (U : ((Σ k, J k) → ℂ) → ℝ) (M : XModel Dc) (S' : BoundedRegularisationSetting M Dc.Xo Hd.aMu (corrW Hd U)) (z : Sp ℂ ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ) (x : ℝ), Or.𝔐.IsCuspWeight Or.sm U → CoordsAt Or.𝔐.ξ Dc.y z w → Or.PhiWeight z w x → x ≤ S'.B.ph (M.proj w) + Real.log (S'.ref.h w) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.cusp_intersection_finite
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_intersection_height : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B : ℕ) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ Or.𝔐.X) (P : AbPart Or.𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V) (w : (Σ k, J k) → L) (r k : ℕ) (v : Fin r → V) (q : CMType H → Fin k → A.Λ), Or.Good → CoordsAt Or.𝔐.ξ Dc.y (spMap (algebraMap (𝓞 L) L) ≫ z) w → Or.𝔐.IsLinPtOf z P MV A → IsOFamily A.ρ A.I v → (∀ τ, A.IsAdapted (Or.sm τ) v (q τ) ∧ ∀ i, (q τ i : V) ∈ A.eig (Or.sm τ)) → ∃ x : (L →+* ℂ) → ℝ, (∀ e : L →+* ℂ, Or.PhiWeight (spMap e ≫ spMap (algebraMap (𝓞 L) L) ≫ z) (fun p => e (w p)) (x e)) ∧ Ht.ptHt (fun k => (muTwDeg Hd B k : ℝ)) (twW (D := Dc) B fun _ => 0) L w + (∑ e : L →+* ℂ, x e) / Module.finrank ℚ L = -A.phiDeg Or.sm (fun τ => Or.𝔐.FibLat (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)) z P MV) v q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.g_height | exact GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.g_height | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.g_height <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.small_points_over_number_field : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L₀ : Type) [Field L₀] [NumberField L₀], 1 ≤ D.p + D.q → ∀ w ∈ Small.ptsOver L₀ (mCoordIdeal y), ∃ (L : Type) (_ : Field L) (_ : NumberField L) (e : L₀ →+* L) (z : Sp (𝓞 L) ⟶ 𝔐.X) (P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) (_ : AddCommGroup V) (_ : Module L V) (_ : Module (𝓞 L) V) (_ : IsScalarTower (𝓞 L) L V) (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V), CoordsAt 𝔐.ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) (fun p => e (w p)) ∧ 𝔐.IsLinPtOf z P MV A ∧ (∀ s, Module.finrank L (eigSp A.ρ (A.σ s)) = labelRk D s) ∧ Module.finrank (𝓞 L) A.Bq.carrier ≤ Fintype.card (CMType H) * (D.p + D.q) := by
  first | exact @LevelTowerAlt.integral_point_extends_compact | exact LevelTowerAlt.integral_point_extends_compact
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_points_over_number_field : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L₀ : Type) [Field L₀] [NumberField L₀], 1 ≤ D.p + D.q → ∀ w ∈ Small.ptsOver L₀ (mCoordIdeal y), ∃ (L : Type) (_ : Field L) (_ : NumberField L) (e : L₀ →+* L) (z : Sp (𝓞 L) ⟶ 𝔐.X) (P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) (_ : AddCommGroup V) (_ : Module L V) (_ : Module (𝓞 L) V) (_ : IsScalarTower (𝓞 L) L V) (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V), CoordsAt 𝔐.ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) (fun p => e (w p)) ∧ 𝔐.IsLinPtOf z P MV A ∧ (∀ s, Module.finrank L (eigSp A.ρ (A.σ s)) = labelRk D s) ∧ Module.finrank (𝓞 L) A.Bq.carrier ≤ Fintype.card (CMType H) * (D.p + D.q) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.small_points_over_number_field
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
namespace GlobalTheory.CompanionTheory.Ar.Cusp.U4

open LevelTowerAlt GlobalTheory.CompanionTheory.Ar.Fl GroundTheory.Heights₂.Heights

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem flat_point_of_principal_sign (hG : Top.Given) (hF : FlatDegree) {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : Host E) {L : Type} [Field L] [NumberField L] (t : SAB H (Sp L)) (ht : IsPrincipal t) (ρ : L) (p' q' : ℕ)
    (σ : L →+* ℂ) (hσ : σ ρ = H.rt0)
    (hs : ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k) (τ : 𝓞 E →+* k),
      (τ H.rt = g ρ → LieMult t.act (spMap g) τ p') ∧ (τ H.rt ≠ g ρ → LieMult t.act (spMap g) τ q'))
    (h1 : 1 ≤ p' + q') (τ : E →+* ℂ) (hτ : τ (H.rt : E) = H.rt0) [NeZero H.d] (χ : DirichletCharacter ℂ H.d)
    (hχ : GlobalTheory.IsKroneckerChar χ) :
    ∃ (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (_ : NumberField c.F) (F : Type) (_ : Field F)
      (_ : NumberField F) (β : c.F →+* F) (e : L →+* F) (io : F →+* ℂ) (tK : SAB H (Sp F)) (_ : SABMap tK t (spMap e))
      (y : Sp F ⟶ Xo.XF c) (_ : SABMap tK Xo.univ.t (under y)) (U : Set (Xo.XF c)) (φ : FrameFn Xo c)
      (N : LogNorms c.F), D.p = p' ∧ D.q = q' ∧ (∀ x, io (β x) = (x : ℂ)) ∧ (∀ x, io (e x) = σ x) ∧
      y ≫ pullback.snd _ _ = spMap β ∧ Set.range y ⊆ U ∧ IsLineFn U τ φ ∧ (∀ s, HasInfNorm U τ φ s (N.inf s)) ∧
      (∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), HasFinNorm U τ φ p κ (N.fin p κ)) ∧ N.IsAdelic ∧
      N.deg = ((p' : ℝ) - q') / 2 * (GlobalTheory.CM.logOm E χ).re := by
  obtain ⟨⟨hP, hN, -, -⟩, -, -, -, hResK, -, -, hGaga, -⟩ := hG
  obtain ⟨D, rfl, rfl, ⟨I⟩⟩ := GlobalTheory.T.tate_iso_datum_exists E H L t ht σ p' q' fun τ => by
    have := hs ℂ σ τ
    rwa [hσ] at this
  let Xo : ∀ l : Level H, Moduli D l := fun l => (hN E H D l h1).some
  obtain ⟨l, hA, hg⟩ := GlobalTheory.GlobalModelGuards.exists_good_level H
  obtain ⟨c₀⟩ := GlobalTheory.ModuliProbe.coeff_nonempty l
  obtain ⟨-, c, -, hc⟩ := GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed E H D l (Xo l) c₀ h1
  haveI := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  obtain ⟨F, hfin, hF', e, o, he, ⟨m⟩⟩ := SabModel.exists_obj_ext E H D l L t ht hA ρ σ hσ hs I c.F c.fin c.le
  haveI : NumberField F := { to_charZero := inferInstance, to_finiteDimensional := hfin }
  obtain ⟨f, ⟨hf, ⟨mf⟩⟩, -⟩ := (Xo l).rep (Sp F) _ inferInstance o
  let bF : c.F →+* F := (IntermediateField.inclusion hF').toRingHom
  let y : Sp F ⟶ (Xo l).XF c := pullback.lift f (spMap bF) (by
    rw [hf, ← Spec.map_comp]
    rfl)
  have hy1 : y ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _
  have hy2 : y ≫ pullback.snd _ _ = spMap bF := pullback.lift_snd _ _ _
  let x₀ : (Xo l).XF c := y (IsLocalRing.closedPoint F)
  let Z : Formalism.L2.Pj.Comp (Xo l) c := ⟨irreducibleComponent x₀, irreducibleComponent_mem_irreducibleComponents x₀⟩
  have hyZ : Set.range y ⊆ (Z : Set ((Xo l).XF c)) := by
    rintro _ ⟨s, rfl⟩
    rw [Subsingleton.elim s (IsLocalRing.closedPoint F)]
    exact mem_irreducibleComponent
  obtain ⟨V, hV, -⟩ := GlobalTheory.UnifFamily.exists_unf_family E H D l (Xo l) c h1
  obtain ⟨g, ty, FU, i, hty, hper⟩ := GlobalTheory.T.exists_family_uniformisation E H D l (Xo l) c Z (D.p + D.q) (V c.F.val.toRingHom).toPj h1
    (hV c.F.val.toRingHom (show Formalism.L2.Pj.GoodEmb c c.F.val.toRingHom from rfl)).1 (hc c le_rfl Z)
  have hclo : IsClopen (Z : Set ((Xo l).XF c)) :=
    Formalism.L2.Pj.CompSplitPfB.cspB_isClopen (Formalism.L2.Pj.CompSplitPfD.cspD_comp_disj (Xo l) c) Z
  obtain ⟨φ, N, hfg, hn, -⟩ := GlobalTheory.T.flat_theorem_of_resolution_gaga hResK hGaga hP E H D Xo l c (Z : Set ((Xo l).XF c)) τ g ty FU i h1 hτ hg
    hty hclo Z.2.1 hper
  let N' : LogNorms c.F := ⟨N.inf, fun p κ => N.fin p κ +
    D.q * (logIdeal (κ.comp (tauIn c τ)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖((H.d : ℕ) : ℂ_[p])‖)⟩
  obtain ⟨had, hdeg⟩ := GlobalTheory.T.kronecker_character_period_formula hF E H D l (Xo l) c g ty FU i _ τ φ N' χ hχ hty hτ hfg hn.1 hn.2
  exact ⟨D, l, Xo l, c, inferInstance, F, inferInstance, inferInstance, bF, e, F.val.toRingHom, o.t, m, y,
    ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast mf.toSABMap hy1.symm, Z, φ, N', rfl, rfl, fun _ => rfl, he, hy2, hyZ, hfg.line, hn.1,
    hn.2, had, hdeg⟩

theorem flat_hermitian_fibre_signature (hG : Top.Given) (hF : FlatDegree) (H : Host E) {L : Type} [Field L] [NumberField L]
    {t' : SAB H (Sp (𝓞 L))} {tB : SAB H (Sp L)} (m' : SABMap tB t' (spMap (algebraMap (𝓞 L) L)))
    {B : HermitianBundle.{0} L} (MB : LieModel t'.G (𝟙 _) B.carrier) {ρM : 𝓞 E →+* Module.End (𝓞 L) B.carrier}
    (s₁ s₂ : 𝓞 E →+* 𝓞 L) (hP : IsPrincipal tB) (hfib : IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) B MB)
    (hρ : MB.IsActOf t'.act.act ρM) (ρ : L) (p' q' : ℕ) (σ : L →+* ℂ) (hσ : σ ρ = H.rt0)
    (hs : ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k) (τ : 𝓞 E →+* k),
      (τ H.rt = g ρ → LieMult tB.act (spMap g) τ p') ∧ (τ H.rt ≠ g ρ → LieMult tB.act (spMap g) τ q'))
    (τ : E →+* ℂ) (hτ : τ (H.rt : E) = H.rt0) (h₁ : ∀ a, σ (s₁ a : L) = τ (a : E))
    (h₂ : ∀ a, σ (s₂ a : L) = starRingEnd ℂ (τ (a : E))) [NeZero H.d] (χ : DirichletCharacter ℂ H.d)
    (hχ : GlobalTheory.IsKroneckerChar χ) :
    |B.normDegree (eigSp ρM s₁) - B.normDegree (eigSp ρM s₂)| ≤
      ((B.rank (eigSp ρM s₁) : ℝ) + B.rank (eigSp ρM s₂)) * |(GlobalTheory.CM.logOm E χ).re| := by
  have r₁ : B.rank (eigSp ρM s₁) = p' := rank_eig MB hρ m' σ s₁ ((hs ℂ σ _).1 ((h₁ _).trans (hτ.trans hσ.symm)))
  have r₂ : B.rank (eigSp ρM s₂) = q' := rank_eig MB hρ m' σ s₂ ((hs ℂ σ _).2 fun h => by
    have h3 := (h₂ H.rt).symm.trans (h.trans hσ)
    rw [hτ, (rt0_conj_neg_ne_zero H).1] at h3
    exact (rt0_conj_neg_ne_zero H).2 (by linear_combination (-1 / 2 : ℂ) * h3))
  rcases Nat.eq_zero_or_pos (p' + q') with h0 | h0
  · have e₁ : eigSp ρM s₁ = ⊥ := Submodule.finrank_eq_zero.1 (r₁.trans (by omega))
    have e₂ : eigSp ρM s₂ = ⊥ := Submodule.finrank_eq_zero.1 (r₂.trans (by omega))
    rw [e₁, e₂, sub_self, abs_zero]
    positivity
  obtain ⟨D, l, Xo, c, _, F, _, _, β, e, io, tK, mo, y, mf, U, φ, N, rfl, rfl, hβ, he, hy, hU, hφ, hinf, hfin, had,
    hdeg⟩ := flat_point_of_principal_sign hG hF H tB hP ρ p' q' σ hσ hs h0 τ hτ χ hχ
  obtain ⟨n₀, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m' mo
  let n : SABMap tK t' (spMap (e.comp (algebraMap (𝓞 L) L))) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast n₀ (LevelTowerAlt.spMap_comp _ _).symm
  have hs₁ : β.comp (tauIn c τ) = (e.comp (algebraMap (𝓞 L) L)).comp s₁ :=
    RingHom.ext fun a => io.injective ((hβ _).trans ((he _).trans (h₁ a)).symm)
  have hs₂ : β.comp (tauIn c (ComplexEmbedding.conjugate τ)) = (e.comp (algebraMap (𝓞 L) L)).comp s₂ :=
    RingHom.ext fun a => io.injective ((hβ _).trans ((he _).trans (h₂ a)).symm)
  obtain ⟨vK, vec, k1, k2, -, k4, k5⟩ := exists_vec MB hρ n mf _
    (e.injective.comp (IsFractionRing.injective (𝓞 L) L)) (𝟙 _) (Category.id_comp _) (under y)
    (Category.id_comp _).symm
  obtain ⟨x₁, hx₁⟩ := exists_smul_mem_span B _ r₁
  obtain ⟨x₂, hx₂⟩ := exists_smul_mem_span B _ r₂
  obtain ⟨N₁, a₁, d₁, i₁, f₁⟩ := exists_logNorms B _ x₁ hx₁.1 hx₁.2.1 r₁
  obtain ⟨N₂, a₂, d₂, i₂, f₂⟩ := exists_logNorms B _ x₂ hx₂.1 hx₂.2.1 r₂
  have hfr : IsFramed U τ β y (fun k => vec (x₁ k)) fun k => vec (x₂ k) :=
    ⟨hy, hU, hs₁ ▸ k4 s₁ _ x₁ hx₁.1 hx₁.2.1 hx₁.2.2, hs₂ ▸ k4 s₂ _ x₂ hx₂.1 hx₂.2.1 hx₂.2.2⟩
  have key := deg_eq_sub β e N N₁ N₂ _ (hφ.ne F β y _ _ hfr) had a₁ a₂
    (fun s => by
      rw [i₁, i₂]
      exact inf_norm MB hρ hfib n mf hy hU hφ hs₁ hs₂ k1 k2 hx₁ hx₂ hfr s (hinf _))
    fun p j => by
      obtain ⟨y₁, u₁, T₁, a1, a2, a3, a4, a5, a6, a7⟩ := f₁ p (j.comp e)
      obtain ⟨y₂, u₂, T₂, b1, b2, b3, b4, b5, b6, b7⟩ := f₂ p (j.comp e)
      rw [a7, b7]
      exact fin_norm MB hρ n mf hy hU hφ hs₁ hs₂ k1 k2 k4 k5 hfr p j a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 (hfin p _)
  rw [← d₁, ← d₂, ← key, hdeg, r₁, r₂, abs_mul]
  refine mul_le_mul_of_nonneg_right (abs_le.2 ⟨?_, ?_⟩) (abs_nonneg _) <;>
    linarith [(Nat.cast_nonneg D.p : (0 : ℝ) ≤ D.p), (Nat.cast_nonneg D.q : (0 : ℝ) ≤ D.q)]

theorem flat_saturation_of_degree (hG : Top.Given) (hF : FlatDegree) : FlatSat := by
  obtain ⟨C, hC, hlog⟩ := logOm_bound
  refine ⟨C, hC, ?_⟩
  intro E _ _ _ H L _ _ t' tB m' B MB ρM s₁ s₂ hP hfib hρ ⟨ρ, p', q', hρ2, hs⟩ hinj hconj
  obtain ⟨_, χ, hχ, hb⟩ := hlog E H
  obtain ⟨σ, hσ⟩ := SabModel.exists_embedding_rt0 H ρ hρ2
  have hi : Function.Injective ((σ.comp (algebraMap (𝓞 L) L)).comp s₁) :=
    (σ.injective.comp (IsFractionRing.injective (𝓞 L) L)).comp hinj
  let τ : E →+* ℂ := IsFractionRing.lift hi
  have hτ : ∀ a : 𝓞 E, σ (s₁ a : L) = τ (a : E) := fun a => (IsFractionRing.lift_algebraMap hi a).symm
  have hsq : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    rw [← hτ, H.sqrt_neg_disc_sq]
    have := congrArg ((σ.comp (algebraMap (𝓞 L) L)).comp s₁) H.rt_sq
    rw [map_pow, map_neg, map_natCast] at this
    exact this
  have h : |B.normDegree (eigSp ρM s₁) - B.normDegree (eigSp ρM s₂)| ≤
      ((B.rank (eigSp ρM s₁) : ℝ) + B.rank (eigSp ρM s₂)) * |(GlobalTheory.CM.logOm E χ).re| := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · exact flat_hermitian_fibre_signature hG hF H m' MB s₁ s₂ hP hfib hρ ρ p' q' σ hσ hs τ h hτ (fun a => by rw [hconj, hτ]) χ hχ
    · rw [abs_sub_comm, add_comm]
      refine flat_hermitian_fibre_signature hG hF H m' MB s₂ s₁ hP hfib hρ ρ p' q' σ hσ hs ((starRingEnd ℂ).comp τ) ?_
        (fun a => by rw [hconj, hτ]; rfl) (fun a => by rw [hτ]; exact (Complex.conj_conj _).symm) χ hχ
      rw [RingHom.comp_apply, h, map_neg, (rt0_conj_neg_ne_zero H).1, neg_neg]
  refine h.trans ?_
  rw [_root_.mul_comm C, _root_.mul_assoc]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

end GlobalTheory.CompanionTheory.Ar.Cusp.U4

set_option maxHeartbeats 1000000 in

theorem _root_.GlobalTheory.CompanionTheory.Relay.phiDeg_fibLat_le_of_isOFamily_of_isAdapted : Top.Given → Fl.FlatDegree → ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ B : ℕ) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ Or.𝔐.X) (P : AbPart Or.𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V) (r k : ℕ) (v : Fin r → V) (q : CMType H → Fin k → A.Λ), admitted Xo l c Y Or B₁ → 4 * Dc.f * Dc.N ^ 2 ≤ B → Or.𝔐.IsLinPtOf z P MV A → Module.finrank (𝓞 L) A.Bq.carrier ≤ Fintype.card (CMType H) * (D.p + D.q) → r + k = Dc.j' → IsOFamily A.ρ A.I v → (∀ τ, A.IsAdapted (Or.sm τ) v (q τ) ∧ ∀ i, (q τ i : V) ∈ A.eig (Or.sm τ)) → A.phiDeg Or.sm (fun τ => Or.𝔐.FibLat (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)) z P MV) v q ≤ C * Dc.f * Dc.j' * abelian₂ B (hostRd E) (hostLval H) :=
  LevelTowerAlt.height_comparison_global_model GlobalTheory.CompanionTheory.Ar.Cusp.U4.flat_saturation_of_degree
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phiDeg_fibLat_le_of_isOFamily_of_isAdapted : Top.Given → Fl.FlatDegree → ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ B : ℕ) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ Or.𝔐.X) (P : AbPart Or.𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V) (r k : ℕ) (v : Fin r → V) (q : CMType H → Fin k → A.Λ), admitted Xo l c Y Or B₁ → 4 * Dc.f * Dc.N ^ 2 ≤ B → Or.𝔐.IsLinPtOf z P MV A → Module.finrank (𝓞 L) A.Bq.carrier ≤ Fintype.card (CMType H) * (D.p + D.q) → r + k = Dc.j' → IsOFamily A.ρ A.I v → (∀ τ, A.IsAdapted (Or.sm τ) v (q τ) ∧ ∀ i, (q τ i : V) ∈ A.eig (Or.sm τ)) → A.phiDeg Or.sm (fun τ => Or.𝔐.FibLat (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)) z P MV) v q ≤ C * Dc.f * Dc.j' * abelian₂ B (hostRd E) (hostLval H) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.phiDeg_fibLat_le_of_isOFamily_of_isAdapted
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.TopHt

open MvPolynomial

section Places

variable {L : Type} [Field L] [NumberField L]

lemma log_iSup_support {Jx : Type} [Fintype Jx] (x : Jx → L) (hx : ∃ i, x i ≠ 0) :
    (Function.support fun v : FinitePlace L => Real.log (⨆ i, v (x i))).Finite := by
  classical
  obtain ⟨i₀, hi₀⟩ := hx
  haveI : Nonempty Jx := ⟨i₀⟩
  have hS : (⋃ i ∈ Finset.univ.filter (fun i => x i ≠ 0),
      Function.mulSupport fun v : FinitePlace L => v (x i)).Finite := by
    refine Set.Finite.biUnion (Finset.finite_toSet _) fun i hi => ?_
    exact FinitePlace.mulSupport_finite (by simpa using hi)
  refine hS.subset fun v hv => ?_
  by_contra hn
  apply hv
  have h1 : ∀ i, x i ≠ 0 → v (x i) = 1 := by
    intro i hi
    by_contra h
    exact hn (Set.mem_biUnion (by simpa using hi) h)
  have h2 : ∀ i, v (x i) ≤ 1 := by
    intro i
    by_cases hi : x i = 0
    · simp [hi]
    · exact (h1 i hi).le
  have h3 : (⨆ i, v (x i)) = 1 := by
    have hle : (⨆ i, v (x i)) ≤ 1 := ciSup_le h2
    have hge : (1 : ℝ) ≤ ⨆ i, v (x i) := by
      have hb : BddAbove (Set.range fun i => v (x i)) := (Set.finite_range _).bddAbove
      calc (1 : ℝ) = v (x i₀) := (h1 i₀ hi₀).symm
        _ ≤ _ := le_ciSup hb i₀
    exact le_antisymm hle hge
  simp [h3]

lemma blocks_support {K : Type} [Fintype K] {Jx : K → Type} [∀ k, Fintype (Jx k)] (a : K → ℝ)
    (x : ∀ k, Jx k → L) (hx : ∀ k, ∃ i, x k i ≠ 0) :
    (Function.support fun v : FinitePlace L => ∑ k, a k * Real.log (⨆ i, v (x k i))).Finite := by
  refine (Set.finite_iUnion fun k => log_iSup_support (x k) (hx k)).subset fun v hv => ?_
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  exact Set.mem_iUnion.2 ⟨k, right_ne_zero_of_mul hk⟩

end Places

variable {K : Type} [Fintype K] {Jx : K → Type} [∀ k, Fintype (Jx k)]

lemma lineHt_decomp (M A : HermLine Jx) (a : K → ℤ) (p q : ℕ) (φ G : ((Σ k, Jx k) → ℂ) → ℝ) (L : Type) [Field L]
    [NumberField L] (w : (Σ k, Jx k) → L) (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) (ha : M.a = (q : ℤ) • a + (p : ℤ) • A.a)
    (hh : ∀ σ : L →+* ℂ, Real.log (M.h fun x => σ (w x)) =
      q * (φ (fun x => σ (w x)) + G (fun x => σ (w x))) + p * Real.log (A.h fun x => σ (w x))) :
    Ht.lineHt M L w = q * (Ht.ptHt (fun k => (a k : ℝ)) φ L w +
      (∑ σ : L →+* ℂ, G (fun x => σ (w x))) / Module.finrank ℚ L) + p * Ht.lineHt A L w := by
  classical
  have hd : (Module.finrank ℚ L : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have s1 := blocks_support (L := L) (fun k => (a k : ℝ)) (fun k i => w ⟨k, i⟩) hw
  have s2 := blocks_support (L := L) (fun k => (A.a k : ℝ)) (fun k i => w ⟨k, i⟩) hw
  have hfin : (∑ᶠ v : FinitePlace L, ∑ k, (M.a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩))) =
      q * (∑ᶠ v : FinitePlace L, ∑ k, (a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩))) +
        p * ∑ᶠ v : FinitePlace L, ∑ k, (A.a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩)) := by
    rw [mul_finsum, mul_finsum, ← finsum_add_distrib]
    · refine finsum_congr fun v => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ha]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast]
      ring
    · exact s1.subset (Function.support_mul_subset_right _ _)
    · exact s2.subset (Function.support_mul_subset_right _ _)
  have harch : ∑ σ : L →+* ℂ, Real.log (M.h fun x => σ (w x)) =
      q * (∑ σ : L →+* ℂ, φ (fun x => σ (w x)) + ∑ σ : L →+* ℂ, G (fun x => σ (w x))) +
        p * ∑ σ : L →+* ℂ, Real.log (A.h fun x => σ (w x)) := by
    rw [Finset.sum_congr rfl fun σ _ => hh σ, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_add_distrib]
  unfold Ht.lineHt Ht.ptHt
  simp only []
  rw [hfin, harch]
  field_simp
  ring

lemma mem_mcPts_of_ptsOver {P : Ideal (MRing Jx)} {L : Type} [Field L] (σ : L →+* ℂ) {w : (Σ k, Jx k) → L}
    (hw : w ∈ Small.ptsOver L P) : (fun p => σ (w p)) ∈ mcPts P := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hw.1 k
    exact ⟨i, (map_ne_zero σ).2 hi⟩
  · have h1 : aeval (fun p => σ (w p)) f = σ (aeval w f) :=
      (comp_aeval_apply (R := ℤ) (f := w) σ.toIntAlgHom f).symm
    rw [MvPolynomial.eval_map, ← algebraMap_int_eq, ← MvPolynomial.aeval_def, h1, hw.2 f hf, map_zero]

end GlobalTheory.CompanionTheory.Ar.Cusp.TopHt

namespace GlobalTheory.CompanionTheory.Ar.Cusp.TopHt

theorem htU_of_given : Top.Given → Fl.FlatDegree → ∃ Ch : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H)
    (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type)
    [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc)
    (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ : ℕ) (U : ((Σ k, J k) → ℂ) → ℝ) (M : XModel Dc)
    (S' : BoundedRegularisationSetting M Dc.Xo Hd.aMu (corrW Hd U)), IsFullIntersectionSystem II → admitted Xo l c Y Or B₁ →
      Or.𝔐.IsCuspWeight Or.sm U → S'.IsTied → HtU S' Ch (hostRd E) (hostLval H) := by
  intro hG hF
  obtain ⟨C, -, hU4⟩ := GlobalTheory.T.phiDeg_fibLat_le_of_isOFamily_of_isAdapted hG hF
  refine ⟨C, ?_⟩
  intro E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B₁ U M S' hII hAdm hU hTied
  intro B p q hB hp hpq
  have hq0 : 0 < q := by omega
  have hq : (0 : ℝ) < q := by exact_mod_cast hq0
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (GlobalTheory.T.regularized_weight_dominates_eventually K J II (CMType H) Ω W Dc Hd M _ S' hTied)
  refine ⟨u / 2, half_pos hu, fun t' ht' ht'u P hP hyP => ?_⟩
  obtain ⟨hge, -, hreg⟩ := hsub ⟨ht', by linarith⟩
  obtain ⟨hsm, hdeg, hlog⟩ := hreg B p q
  obtain ⟨L₀, _, _, w, -, hw, hII'⟩ := GlobalTheory.T.height_of_zero_dim_variety K J II hII.1 P hP
  have hdeg0 : (0 : ℝ) < degC P := Nat.cast_pos.2 (degC_pos_of_isArithVar_one hP)
  have hMU : htMUc Hd S' B p q t' P = Ht.lineHt (MUc Hd S' B p q t') L₀ w / q := by
    unfold htMUc
    rw [← hII' _ hsm]
    field_simp
  have hA' : -Dc.KA ≤ Ht.lineHt Dc.A' L₀ w := by
    rw [← hII' _ Dc.A'_pos.1, le_div_iff₀ hdeg0]
    linarith [Dc.heights P hP hyP]
  have hwy : w ∈ Small.ptsOver L₀ (mCoordIdeal Dc.y) := ⟨hw.1, fun f hf => hw.2 f (hyP hf)⟩
  have hpq1 : 1 ≤ D.p + D.q := by
    have h1 := Or.N_eq
    have h2 := Dc.two_le_N
    omega
  obtain ⟨L, _, _, e, z, Pa, V, _, _, _, _, MV, A, hco, hlin, hrk, hBq⟩ :=
    GlobalTheory.T.small_points_over_number_field hG E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 L₀ hpq1 w hwy
  obtain ⟨-, -, -, -, -, hcard, -⟩ :=
    GlobalTheory.T.cusp_correspondence_bound E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 L (spMap (algebraMap (𝓞 L) L) ≫ z)
  obtain ⟨⟨r, v, hv⟩, hadp⟩ := GlobalTheory.T.adapted_family_exists_on_eigenspace E L (CMType H) V A hcard
  have hne : Nonempty (CMType H) := by
    have h1 : 0 < Module.finrank ℚ E := Module.finrank_pos
    rw [← hcard] at h1
    exact Fintype.card_pos_iff.1 (by omega)
  obtain ⟨τ₀⟩ := hne
  have hrj : r + (Dc.j' - r) = Dc.j' := by
    obtain ⟨k, -, -, -, h3, -⟩ := hadp r v hv (Or.sm τ₀)
    rw [hrk, Or.rk_sm] at h3
    unfold ComponentData.j'
    omega
  have hk : ∀ τ, ∃ qq : Fin (Dc.j' - r) → A.Λ, (∀ i, (qq i : V) ∈ A.eig (Or.sm τ)) ∧
      A.IsAdapted (Or.sm τ) v qq := by
    intro τ
    obtain ⟨k, qq, h1, h2, h3, -⟩ := hadp r v hv (Or.sm τ)
    have hk' : k = Dc.j' - r := by
      rw [hrk, Or.rk_sm] at h3
      unfold ComponentData.j'
      omega
    subst hk'
    exact ⟨qq, h1, h2⟩
  choose qq hqq1 hqq2 using hk
  obtain ⟨x, hx, hht⟩ := GlobalTheory.T.cusp_intersection_height hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B L z Pa V MV A
    (fun p => e (w p)) r (Dc.j' - r) v qq hAdm.2.1 hco hlin hv (fun τ => ⟨hqq2 τ, hqq1 τ⟩)
  have hu4 := hU4 E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B₁ B L z Pa V MV A r (Dc.j' - r) v qq hAdm hB hlin hBq
    hrj hv (fun τ => ⟨hqq2 τ, hqq1 τ⟩)
  have hxe : ∀ σ : L →+* ℂ, x σ ≤ Real.log (S'.ref.h fun p => σ (e (w p))) +
      S'.bregWeight t' (M.proj fun p => σ (e (w p))) := by
    intro σ
    have hc := RootHt.PullCoords.coordsAt_embedding _ _ Or.𝔐.ξ K J Dc.y L (fun p => e (w p)) z σ hco
    have e1 : spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z = spMap σ ≫ spMap (algebraMap (𝓞 L) L) ≫ z := by
      rw [← Category.assoc, ← Spec.map_comp]
      rfl
    rw [e1] at hc
    have h1 := GlobalTheory.T.cusp_intersection_finite hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or U M S' _ _ (x σ) hU hc (hx σ)
    linarith [hge (M.proj fun p => σ (e (w p)))]
  have hext : ∀ A₀ : HermLine J, Ht.lineHt A₀ L (fun p => e (w p)) = Ht.lineHt A₀ L₀ w := by
    intro A₀
    have h1 := GlobalTheory.T.line_height_invariant_scaling K J A₀ L₀ L e w (fun _ => 1) hw.1 (fun _ => one_ne_zero)
    simpa using h1
  have hw' : ∀ k, ∃ i, e (w ⟨k, i⟩) ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hw.1 k
    exact ⟨i, (map_ne_zero e).2 hi⟩
  have hdec := lineHt_decomp (MUc Hd S' B p q t') Dc.A' (muTwDeg Hd B) p q (twW (D := Dc) B fun _ => 0)
    (fun z' => Real.log (S'.ref.h z') + S'.bregWeight t' (M.proj z')) L (fun p => e (w p)) hw'
    (by rw [hdeg, Dc.A'_deg]) (fun σ => by
      have hm := mem_mcPts_of_ptsOver (σ.comp e) hwy
      simp only [RingHom.comp_apply] at hm
      rw [hlog _ hm]
      simp only [twW, RingHom.comp_apply, zero_add]
      ring)
  rw [hext, hext] at hdec
  have hsum : ∑ σ : L →+* ℂ, x σ ≤ ∑ σ : L →+* ℂ, (Real.log (S'.ref.h fun p => σ (e (w p))) +
      S'.bregWeight t' (M.proj fun p => σ (e (w p)))) := Finset.sum_le_sum fun σ _ => hxe σ
  have hn : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  have hdiv := div_le_div_of_nonneg_right hsum hn.le
  have hpq' : (0 : ℝ) ≤ p / q := div_nonneg (Nat.cast_nonneg _) hq.le
  rw [hMU, hdec]
  have hAq : -(p / q * Dc.KA) ≤ p / q * Ht.lineHt Dc.A' L₀ w := by nlinarith
  rw [show (q * (Ht.ptHt (fun k => (muTwDeg Hd B k : ℝ)) (twW (D := Dc) B fun _ => 0) L (fun p => e (w p)) +
      (∑ σ : L →+* ℂ, (Real.log (S'.ref.h fun p => σ (e (w p))) + S'.bregWeight t' (M.proj fun p => σ (e (w p))))) /
        Module.finrank ℚ L) + p * Ht.lineHt Dc.A' L₀ w) / q =
      Ht.ptHt (fun k => (muTwDeg Hd B k : ℝ)) (twW (D := Dc) B fun _ => 0) L (fun p => e (w p)) +
      (∑ σ : L →+* ℂ, (Real.log (S'.ref.h fun p => σ (e (w p))) + S'.bregWeight t' (M.proj fun p => σ (e (w p))))) /
        Module.finrank ℚ L + p / q * Ht.lineHt Dc.A' L₀ w by field_simp]
  linarith

end GlobalTheory.CompanionTheory.Ar.Cusp.TopHt
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_height_upper : Top.Given → Fl.FlatDegree → ∃ Ch : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ : ℕ) (U : ((Σ k, J k) → ℂ) → ℝ) (M : XModel Dc) (S' : BoundedRegularisationSetting M Dc.Xo Hd.aMu (corrW Hd U)), IsFullIntersectionSystem II → admitted Xo l c Y Or B₁ → Or.𝔐.IsCuspWeight Or.sm U → S'.IsTied → HtU S' Ch (hostRd E) (hostLval H) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Cusp.TopHt.htU_of_given
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem pieces_nonempty : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd), Nonempty (Pieces Or) :=
  @SheetDecomposition.sheet_pieces_existence

end GlobalTheory.CompanionTheory.Ar.Cusp
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_volume_left : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd), Nonempty (Pieces Or) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Cusp.pieces_nonempty
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem ptsIntegral_eq_sum_fundamental : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (Q : Pieces Or), ∃ κ : ℝ, 0 < κ ∧ ∀ (G : ((Σ k, J k) → ℂ) → ℝ) (Gk : Fin Q.np → (Fin Dc.n → ℂ) → ℝ), (∀ w ∈ Dc.Xo, ∀ w' ∈ torusSat {w}, G w' = G w) → (∀ m, ∀ t ∈ Q.V m, G (Q.γ m t) = Gk (Q.pc m) t) → (∀ k, IntegrableOn (fun t => Gk k t * ballDens (Q.F k).q t) (Q.FF k)) → ptsIntegral (e := Dc.n) (mCoordIdeal Dc.y) (fun _ => phMu Hd) G = κ * ∑ k, (Q.d k : ℝ) * ∫ t in Q.FF k, Gk k t * ballDens (Q.F k).q t :=
  SheetDecomposition.sheet_pieces_component

end GlobalTheory.CompanionTheory.Ar.Cusp
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ptsIntegral_eq_sum_ballDens_integrals : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (Q : Pieces Or), ∃ κ : ℝ, 0 < κ ∧ ∀ (G : ((Σ k, J k) → ℂ) → ℝ) (Gk : Fin Q.np → (Fin Dc.n → ℂ) → ℝ), (∀ w ∈ Dc.Xo, ∀ w' ∈ torusSat {w}, G w' = G w) → (∀ m, ∀ t ∈ Q.V m, G (Q.γ m t) = Gk (Q.pc m) t) → (∀ k, IntegrableOn (fun t => Gk k t * ballDens (Q.F k).q t) (Q.FF k)) → ptsIntegral (e := Dc.n) (mCoordIdeal Dc.y) (fun _ => phMu Hd) G = κ * ∑ k, (Q.d k : ℝ) * ∫ t in Q.FF k, Gk k t * ballDens (Q.F k).q t := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_eq_sum_fundamental
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_volume_middle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (Q : Pieces Or) (U : ((Σ k, J k) → ℂ) → ℝ), Or.𝔐.IsCuspWeight Or.sm U → (∀ w ∈ Dc.Xo, ∀ w' ∈ torusSat {w}, U w' = U w) ∧ ∀ m, ∀ t ∈ Q.V m, U (Q.γ m t) = ((Q.F (Q.pc m)).R t).cuspW (Q.F (Q.pc m)).σ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.WeightSheet.cuspWeight_torus_and_sheets | exact GlobalTheory.CompanionTheory.Ar.Cusp.WeightSheet.cuspWeight_torus_and_sheets | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.WeightSheet.cuspWeight_torus_and_sheets <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

namespace GlobalTheory.CompanionTheory.Ar.Cusp

namespace TopMean

theorem bracket_le (f j' B : ℕ) (rd L : ℝ) (hrd : 2 ≤ rd) (hf : 1 ≤ f) (hj : 1 ≤ j')
    (hB : 2 * f * j' ≤ B) (hB64 : 64 ≤ B) :
    6 + Real.log (2 * (f : ℝ) * rd) + Real.log (2 * (f : ℝ) * j' * rd) ≤
      4 * (Real.log ((B : ℝ) * rd) + |L|) := by
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hj' : (1 : ℝ) ≤ j' := by exact_mod_cast hj
  have hB' : 2 * (f : ℝ) * j' ≤ B := by exact_mod_cast hB
  have hB64' : (64 : ℝ) ≤ B := by exact_mod_cast hB64
  have hrd0 : 0 < rd := by linarith
  have h1 : Real.log (2 * (f : ℝ) * rd) ≤ Real.log ((B : ℝ) * rd) := by
    apply Real.log_le_log (by positivity)
    apply mul_le_mul_of_nonneg_right _ hrd0.le
    nlinarith
  have h2 : Real.log (2 * (f : ℝ) * j' * rd) ≤ Real.log ((B : ℝ) * rd) := by
    apply Real.log_le_log (by positivity)
    exact mul_le_mul_of_nonneg_right hB' hrd0.le
  have h3 : 3 ≤ Real.log ((B : ℝ) * rd) := by
    have h128 : (128 : ℝ) ≤ (B : ℝ) * rd := by nlinarith
    have hl : Real.log (128 : ℝ) = 7 * Real.log 2 := by
      rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_log (by norm_num) h128
    have := Real.log_two_gt_d9
    linarith
  have := abs_nonneg L
  linarith

end TopMean

open TopMean in

theorem top_mean_cusp_weight : Top.Given → ∃ Cu : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ : ℕ) (U : ((Σ k, J k) → ℂ) → ℝ), IsFullIntersectionSystem II → admitted Xo l c Y Or B₁ → Or.𝔐.IsCuspWeight Or.sm U → MeanU Hd U Cu (hostRd E) (hostLval H) := by
  intro hG
  refine ⟨4, ?_⟩
  intro E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B₁ U _ _ hU
  obtain ⟨Q⟩ := GlobalTheory.T.cusp_volume_left hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or
  obtain ⟨κ, hκ, htr⟩ := GlobalTheory.T.ptsIntegral_eq_sum_ballDens_integrals E H D Xo l c Y II K J Ω W Dc Hd S₀ Or Q
  have hw := GlobalTheory.T.cusp_volume_middle E H D Xo l c Y II K J Ω W Dc Hd S₀ Or Q U hU
  obtain ⟨hrd, ⟨τ₀⟩, -⟩ := GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers E H
  intro hj' hN B hB
  have hjN : Dc.j + Dc.j' = Dc.N := by
    have := Dc.j_le; have := Dc.two_le_N
    show Dc.j + (Dc.N - Dc.j) = Dc.N
    omega
  have hball := fun k => GlobalTheory.T.cusp_weight_integrable_on_fundamental_set E (CMType H) Dc.j Dc.j' Dc.n Q.g (Q.Λ k) H (Q.F k) (Q.Γ k) (Q.FF k)
    (Q.arith k) (Q.fund k) hj' (by omega)
  set C : ℝ := (Fintype.card (CMType H) : ℝ) * Dc.j' * (6 + Real.log (2 * Fintype.card (CMType H) * hostRd E) +
    Real.log (2 * Fintype.card (CMType H) * Dc.j' * hostRd E)) with hC
  have hdeg : GroundTheory.Heights₂.Heights.LowerBoundFree.degMu Hd =
      κ * ∑ k, (Q.d k : ℝ) * ∫ t in Q.FF k, ballDens (Q.F k).q t := by
    have e1 : GroundTheory.Heights₂.Heights.LowerBoundFree.degMu Hd =
        ptsIntegral (e := Dc.n) (mCoordIdeal Dc.y) (fun _ => phMu Hd) (fun _ => 1) := rfl
    rw [e1, htr (fun _ => 1) (fun _ _ => 1) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
      (fun k => by simpa using (hball k).1)]
    refine congrArg (κ * ·) (Finset.sum_congr rfl fun k _ => ?_)
    simp
  have hnum : ptsIntegral (e := Dc.n) (mCoordIdeal Dc.y) (fun _ => phMu Hd) U =
      κ * ∑ k, (Q.d k : ℝ) * ∫ t in Q.FF k, ((Q.F k).R t).cuspW (Q.F k).σ * ballDens (Q.F k).q t :=
    htr U (fun k t => ((Q.F k).R t).cuspW (Q.F k).σ) hw.1 hw.2 (fun k => (hball k).2.2.1)
  have hle : ∀ k, (Q.d k : ℝ) * (∫ t in Q.FF k, ((Q.F k).R t).cuspW (Q.F k).σ * ballDens (Q.F k).q t) ≤
      C * ((Q.d k : ℝ) * ∫ t in Q.FF k, ballDens (Q.F k).q t) := fun k => by
    have h := mul_le_mul_of_nonneg_left (hball k).2.2.2 (Nat.cast_nonneg (α := ℝ) (Q.d k))
    calc _ ≤ _ := h
      _ = _ := by rw [hC]; ring
  have hDpos : 0 < GroundTheory.Heights₂.Heights.LowerBoundFree.degMu Hd := by
    rw [hdeg]
    apply mul_pos hκ
    obtain ⟨k0, hk0⟩ := Q.d_pos
    exact Finset.sum_pos' (fun k _ => mul_nonneg (Nat.cast_nonneg _) (hball k).2.1.le)
      ⟨k0, Finset.mem_univ _, mul_pos (by exact_mod_cast hk0) (hball k0).2.1⟩
  have hmean : meanOf Hd U ≤ C := by
    unfold meanOf
    rw [div_le_iff₀ hDpos, hnum]
    calc κ * ∑ k, (Q.d k : ℝ) * (∫ t in Q.FF k, ((Q.F k).R t).cuspW (Q.F k).σ * ballDens (Q.F k).q t)
        ≤ κ * ∑ k, C * ((Q.d k : ℝ) * ∫ t in Q.FF k, ballDens (Q.F k).q t) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hle k) hκ.le
      _ = C * GroundTheory.Heights₂.Heights.LowerBoundFree.degMu Hd := by
          rw [hdeg, ← Finset.mul_sum]; ring
  have hf : 1 ≤ Fintype.card (CMType H) := Fintype.card_pos_iff.mpr ⟨τ₀⟩
  have hfD : Dc.f = Fintype.card (CMType H) := rfl
  have hN4 : 4 ≤ Dc.N := by omega
  have hB64 : 64 ≤ B := by
    have : 4 * 1 * 4 ^ 2 ≤ 4 * Dc.f * Dc.N ^ 2 := by
      rw [hfD]; gcongr
    omega
  have hB2 : 2 * Fintype.card (CMType H) * Dc.j' ≤ B := by
    have hjN' : Dc.j' ≤ Dc.N ^ 2 := le_trans (by omega) (Nat.le_self_pow (by norm_num) _)
    have : 2 * Fintype.card (CMType H) * Dc.j' ≤ 4 * Dc.f * Dc.N ^ 2 := by
      rw [hfD]
      calc 2 * Fintype.card (CMType H) * Dc.j' ≤ 4 * Fintype.card (CMType H) * Dc.N ^ 2 := by
            have := Nat.mul_le_mul_left (4 * Fintype.card (CMType H)) hjN'
            nlinarith
        _ = _ := rfl
    omega
  have hbr := bracket_le (Fintype.card (CMType H)) Dc.j' B (hostRd E) (hostLval H) hrd hf hj' hB2 hB64
  have hfj : (0 : ℝ) ≤ (Fintype.card (CMType H) : ℝ) * Dc.j' := by positivity
  calc meanOf Hd U ≤ C := hmean
    _ ≤ (Fintype.card (CMType H) : ℝ) * Dc.j' * (4 * (Real.log ((B : ℝ) * hostRd E) + |hostLval H|)) := by
        rw [hC]; exact mul_le_mul_of_nonneg_left hbr hfj
    _ = 4 * Dc.f * Dc.j' * abelian₂ B (hostRd E) (hostLval H) := by
        rw [hfD, GroundTheory.Heights₂.Heights.LowerBoundFree.abelian₂]; ring

end GlobalTheory.CompanionTheory.Ar.Cusp
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_volume_sum : Top.Given → ∃ Cu : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ : ℕ) (U : ((Σ k, J k) → ℂ) → ℝ), IsFullIntersectionSystem II → admitted Xo l c Y Or B₁ → Or.𝔐.IsCuspWeight Or.sm U → MeanU Hd U Cu (hostRd E) (hostLval H) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Cusp.top_mean_cusp_weight
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Cusp.TopNine

theorem nineGeoU_of_given (hG : Top.Given) (hW : Out.WeilSt) (hF : Fl.FlatDegree) :
    ∃ Ch Cu : ℝ, NineGeoU Ch Cu := by
  obtain ⟨Ch, hCh⟩ := GlobalTheory.T.cusp_height_upper hG hF
  obtain ⟨Cu, hCu⟩ := GlobalTheory.T.cusp_volume_sum hG
  refine ⟨Ch, Cu, ?_⟩
  intro E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B₁ U M S' hII hAdm hU hT
  exact ⟨GlobalTheory.T.intersection_degree_lower hG hW E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B₁ U M S' hII hAdm hT,
    hCh E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B₁ U M S' hII hAdm hU hT,
    hCu E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B₁ U hII hAdm hU⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.TopNine
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_geometric_height_constants : Top.Given → Out.WeilSt → Fl.FlatDegree → ∃ Ch Cu : ℝ, NineGeoU Ch Cu := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Cusp.TopNine.nineGeoU_of_given
end
