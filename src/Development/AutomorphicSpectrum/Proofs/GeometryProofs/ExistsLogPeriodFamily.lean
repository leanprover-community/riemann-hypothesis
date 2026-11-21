import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsAbLift
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FamilyUniformisationOfAbelianSchemeLaws
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelLabelExtendsOfOrthogonalToExtended
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFamilyExponentialLocally
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeDiscreteFreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodHolomorphicContinuation
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodSetClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExponentialFamilyPeriods
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeGram
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExponentialSurjectiveSemiabelianStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionPointsDivisible
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolPairA
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionSectionEqOfConnected
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsToricTorsionCubWeilOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartHodgeMatrixStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeOnPuncturedDisc
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraTail

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_family_exponential_locally : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)), Smooth G.hom → IsHolPts B ψ → ∀ b₀ ∈ B, ∃ ε : ℝ, 0 < ε ∧ ball b₀ ε ⊆ B ∧ Nonempty (FamExp G M (ball b₀ ε) ψ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_famExp_near | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_famExp_near | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_famExp_near <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open GlobalTheory.Points
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.PerSpan

theorem compact_alt_alt (A : Over (Sp ℂ)) [GrpObj A] (hA : IsAbelianScheme A) :
    CompactSpace (𝟙_ (Over (Sp ℂ)) ⟶ A) ∧ T2Space (𝟙_ (Over (Sp ℂ)) ⟶ A) := by
  have := hA.proper
  obtain ⟨H, m, s, hH, hs, -⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmple ℂ A hA
  have hp : IsProjOver A.hom := (GlobalTheory.isProjOver_iff_isProper_and_exists_isAmpleLB A.hom).2
    ⟨inferInstance, H, GlobalTheory.isAmpleLB_of_veryAmpleBy hs⟩
  have h1 := PtsOver.compactSpace (F := ℂ) hp (𝟙 _)
  have h2 := PtsOver.t2Space (C := ℂ) A.hom (𝟙 _)
  exact ⟨(overHomeomorph A).symm.compactSpace, (overHomeomorph A).symm.t2Space⟩

theorem eq_top_of_compact_quotient (g : ℕ) (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H] (π : (Fin g → ℂ) → H) (hadd : ∀ z w, π (z + w) = π z * π w) (hc : Continuous π)
    (hs : Function.Surjective π) (W : Submodule ℂ (Fin g → ℂ)) (hW : ∀ z, π z = 1 → z ∈ W) : W = ⊤ := by
  by_contra hne
  obtain ⟨ℓ, hℓ, hle⟩ := Submodule.exists_le_ker_of_lt_top W (lt_top_iff_ne_top.2 hne)
  let f : Multiplicative (Fin g → ℂ) →* H := MonoidHom.mk' (fun z => π z.toAdd) fun a b => hadd _ _
  have : SigmaCompactSpace (Multiplicative (Fin g → ℂ)) := inferInstanceAs (SigmaCompactSpace (Fin g → ℂ))
  have hopen : IsOpenMap f := MonoidHom.isOpenMap_of_sigmaCompact f hs hc
  have hU : IsOpen (π '' ball 0 1) := hopen _ (isOpen_ball (x := (0 : Fin g → ℂ)) (ε := 1))
  have h0 : π 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hne' : (interior (π '' ball 0 1)).Nonempty := by
    rw [hU.interior_eq]
    exact ⟨π 0, 0, mem_ball_self one_pos, rfl⟩
  obtain ⟨t, ht⟩ := compact_covered_by_mul_left_translates (isCompact_univ (X := H)) hne'
  choose lift hlift using hs
  let ℓ' := LinearMap.toContinuousLinearMap ℓ
  have heq : ∀ a b, π a = π b → ℓ a = ℓ b := fun a b h => by
    have h1 : π (a - b) = 1 := by
      have := hadd (a - b) b
      rw [sub_add_cancel, h] at this
      exact right_eq_mul.1 this
    have h2 := hle (hW _ h1)
    rwa [LinearMap.mem_ker, map_sub, sub_eq_zero] at h2
  have hbd : ∀ z, ‖ℓ z‖ ≤ ‖ℓ'‖ + ∑ c ∈ t, ‖ℓ (lift c)‖ := fun z => by
    obtain ⟨c, hct, hcz⟩ : ∃ c ∈ t, c * π z ∈ π '' ball 0 1 := by
      have := ht (Set.mem_univ (π z))
      simpa using this
    obtain ⟨w, hw, hwz⟩ := hcz
    have h1 : π w = π (lift c + z) := by rw [hwz, hadd, hlift]
    have h2 := heq _ _ h1
    rw [map_add] at h2
    have h3 : ℓ z = ℓ w - ℓ (lift c) := by rw [h2]; ring
    have h4 : ‖ℓ w‖ ≤ ‖ℓ'‖ := by
      have := ℓ'.le_opNorm w
      have hw' : ‖w‖ ≤ 1 := by simpa using (mem_ball_zero_iff.1 hw).le
      calc ‖ℓ w‖ = ‖ℓ' w‖ := rfl
        _ ≤ ‖ℓ'‖ * ‖w‖ := this
        _ ≤ ‖ℓ'‖ * 1 := by gcongr
        _ = ‖ℓ'‖ := mul_one _
    have h5 : ‖ℓ (lift c)‖ ≤ ∑ c ∈ t, ‖ℓ (lift c)‖ :=
      Finset.single_le_sum (f := fun c => ‖ℓ (lift c)‖) (fun _ _ => norm_nonneg _) hct
    rw [h3]
    exact (norm_sub_le _ _).trans (add_le_add h4 h5)
  obtain ⟨v, hv⟩ : ∃ v, ℓ v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hℓ (LinearMap.ext hcon)
  set C := ‖ℓ'‖ + ∑ c ∈ t, ‖ℓ (lift c)‖
  have hC : 0 ≤ C := (norm_nonneg _).trans (hbd 0)
  have := hbd (((C + 1 : ℝ) / ‖ℓ v‖ : ℂ) • v)
  rw [map_smul, smul_eq_mul, norm_mul] at this
  have hn : ‖ℓ v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  have h6 : ‖((C + 1 : ℝ) / ‖ℓ v‖ : ℂ)‖ * ‖ℓ v‖ = C + 1 := by
    rw [norm_div, Complex.norm_real, Complex.norm_real, norm_norm, Real.norm_eq_abs, abs_of_nonneg (by linarith),
      div_mul_cancel₀ _ hn]
  linarith

section Fibre
variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] (x : Sp ℂ ⟶ Sp R)

def toFibre (p : Over.mk x ⟶ G) : 𝟙_ (Over (Sp ℂ)) ⟶ (Over.pullback x).obj G :=
  Over.homMk (pullback.lift p.left (𝟙 _) (by simpa using Over.w p)) (pullback.lift_snd _ _ _)

def ofFibre (y : 𝟙_ (Over (Sp ℂ)) ⟶ (Over.pullback x).obj G) : Over.mk x ⟶ G :=
  Over.homMk (y.left ≫ pullback.fst G.hom x) (by
    have h := Over.w y
    have h' : y.left ≫ pullback.snd G.hom x = 𝟙 _ := h
    simp only [Over.mk_left, Over.mk_hom, Category.assoc, pullback.condition]
    rw [← Category.assoc, h']
    exact Category.id_comp x)

theorem ofFibre_toFibre (p : Over.mk x ⟶ G) : ofFibre G x (toFibre G x p) = p :=
  Over.OverMorphism.ext (pullback.lift_fst _ _ _)

theorem toFibre_ofFibre (y : 𝟙_ (Over (Sp ℂ)) ⟶ (Over.pullback x).obj G) : toFibre G x (ofFibre G x y) = y := by
  refine Over.OverMorphism.ext ?_
  have h' : y.left ≫ pullback.snd G.hom x = 𝟙 _ := Over.w y
  refine pullback.hom_ext ?_ ?_
  · exact pullback.lift_fst _ _ _
  · exact (pullback.lift_snd _ _ _).trans h'.symm

theorem ofFibre_mul (y y' : 𝟙_ (Over (Sp ℂ)) ⟶ (Over.pullback x).obj G) :
    ofFibre G x (y * y') = ofFibre G x y * ofFibre G x y' := by
  let ρ : Over.mk x ⟶ Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ x) := Over.homMk (𝟙 _) (by simp)
  have e : ∀ a, ofFibre G x a = ρ ≫ Out.toBase pullback.condition a := fun a =>
    Over.OverMorphism.ext (by simp [ofFibre, ρ, Out.toBase])
  rw [e, e, e, GlobalTheory.UU.toBase_mul_pullback, MonObj.comp_mul]

theorem toFibre_mul (p p' : Over.mk x ⟶ G) : toFibre G x (p * p') = toFibre G x p * toFibre G x p' := by
  have := ofFibre_mul G x (toFibre G x p) (toFibre G x p')
  rw [ofFibre_toFibre, ofFibre_toFibre] at this
  rw [← this, toFibre_ofFibre]

end Fibre

theorem ofFibre_one {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] (x : Sp ℂ ⟶ Sp R) :
    ofFibre G x 1 = 1 := by
  have := ofFibre_mul G x 1 1
  rw [_root_.mul_one] at this
  exact left_eq_mul.1 this

theorem isHolTo_slice_at {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V'] [NormedSpace ℂ V']
    {X : Scheme.{0}} {B : Set V} {b : V} (hb : b ∈ B) {c : V × V' → (Sp ℂ ⟶ X)}
    (h : IsHolTo (B ×ˢ Set.univ) c) : IsHolTo Set.univ (fun z => c (b, z)) := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  have hj : Differentiable ℂ (fun z : V' => (b, z)) := (differentiable_const _).prodMk differentiable_id
  refine ⟨?_, ?_⟩
  · have h3 := h1.preimage hj.continuous
    simpa only [Set.preimage_setOf_eq, Set.mem_prod, Set.mem_univ, and_true, hb, true_and] using h3
  · exact h2.comp hj.differentiableOn fun z hz => ⟨⟨hb, trivial⟩, hz.2⟩

theorem isHolTo_ex_slice {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {g n : ℕ}
    {M : LieModel G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}
    (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) :
    IsHolTo Set.univ (fun z => (e.ex b z).left) :=
  isHolTo_slice_at (V := Fin n → ℂ) (V' := Fin g → ℂ) (X := G.left) (b := b) (B := B)
    (c := fun bz => (e.ex bz.1 bz.2).left) hb e.hol

theorem isHolTo_snd {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V'] [NormedSpace ℂ V']
    {X : Scheme.{0}} {c : V' → (Sp ℂ ⟶ X)} (h : IsHolTo Set.univ c) :
    IsHolTo (Set.univ ×ˢ Set.univ) (fun p : V × V' => c p.2) := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  refine ⟨?_, ?_⟩
  · have h3 := h1.preimage (continuous_snd (X := V) (Y := V'))
    simpa only [Set.preimage_setOf_eq, Set.mem_prod, Set.mem_univ, and_self, true_and] using h3
  · exact h2.comp differentiable_snd.differentiableOn fun z hz => ⟨trivial, hz.2⟩

def famExpAtPoint {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {g n : ℕ}
    {M : LieModel G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}
    (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) :
    FamExp G M (Set.univ : Set (Fin 0 → ℂ)) (fun _ => ψ b) where
  ex _ z := e.ex b z
  add _ _ z w := e.add b hb z w
  hol := isHolTo_snd (V := Fin 0 → ℂ) (X := G.left) (c := fun z => (e.ex b z).left) (isHolTo_ex_slice e hb)
  diff _ _ a := e.diff b hb a
  log b₀ _ := by
    obtain ⟨V, N, f, L, h1, h2, h3, h4⟩ := e.log b hb
    have hφ : Continuous (fun p : (Fin 0 → ℂ) × (Fin N → ℂ) => (b, p.2)) := by fun_prop
    have hφ' : Continuous (fun p : (Fin 0 → ℂ) × (Fin g → ℂ) => (b, p.2)) := by fun_prop
    refine ⟨V, N, f, fun p => L (b, p.2), h1, ?_, ?_, ?_⟩
    · exact AnalyticAt.comp' (f := fun p : (Fin 0 → ℂ) × (Fin N → ℂ) => (b, p.2)) h2
        (analyticAt_const.prod analyticAt_snd)
    · exact (hφ'.tendsto (b₀, 0)).eventually h3
    · exact (hφ.tendsto (b₀, _)).eventually h4

theorem exists_linear_lift_at_point (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ)
    (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ))
    (e : FamExp G M B ψ) (b : Fin n → ℂ) (hb : b ∈ B) (m : ℕ) (u : (Fin m → ℂ) → (Over.mk (spMap (ψ b)) ⟶ G))
    (hadd : ∀ z w, u (z + w) = u z * u w) (hhol : IsHolTo Set.univ (fun z => (u z).left)) :
    ∃ h : (Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, e.ex b (h z) = u z := by
  obtain ⟨h, -, hh⟩ := exists_linear_lift_of_additive_family R G g 0 M Set.univ (fun _ => ψ b) (famExpAtPoint e hb) m Set.univ
    (fun _ z => u z) isOpen_univ subset_rfl (fun _ _ z w => hadd z w)
    (isHolTo_snd (V := Fin 0 → ℂ) (X := G.left) (c := fun z => (u z).left) hhol)
  exact ⟨h 0, (hh 0 trivial).1⟩

section TorusExp

def gammaEquiv : Γ(Sp ℂ, ⊤) ≃+* ℂ := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv

def expUnit (z : ℂ) : Γ(Sp ℂ, ⊤)ˣ :=
  Units.map gammaEquiv.symm.toRingHom.toMonoidHom (Units.mk0 (Complex.exp z) (Complex.exp_ne_zero z))

theorem gamma_expUnit (z : ℂ) : gammaEquiv (expUnit z).val = Complex.exp z := gammaEquiv.apply_symm_apply _

theorem expUnit_ext {u v : Γ(Sp ℂ, ⊤)ˣ} (h : gammaEquiv u.val = gammaEquiv v.val) : u = v :=
  Units.ext (gammaEquiv.injective h)

theorem expUnit_add (z w : ℂ) : expUnit (z + w) = expUnit z * expUnit w :=
  expUnit_ext (by rw [Units.val_mul, map_mul, gamma_expUnit, gamma_expUnit, gamma_expUnit, Complex.exp_add])

theorem expUnit_eq_one {z : ℂ} (h : Complex.exp z = 1) : expUnit z = 1 :=
  expUnit_ext (by rw [gamma_expUnit, h, Units.val_one, map_one])

variable {X : Type} [AddCommGroup X] {d : ℕ} (β : Module.Basis (Fin d) ℤ X)

def pairing (w : Fin d → ℂ) (χ : X) : ℂ := ∑ a, ((β.repr χ a : ℤ) : ℂ) * w a

theorem pairing_add_left (z w : Fin d → ℂ) (χ : X) : pairing β (z + w) χ = pairing β z χ + pairing β w χ := by
  simp [pairing, mul_add, Finset.sum_add_distrib]

theorem pairing_add_right (w : Fin d → ℂ) (χ χ' : X) : pairing β w (χ + χ') = pairing β w χ + pairing β w χ' := by
  simp [pairing, add_mul, Finset.sum_add_distrib]

theorem pairing_basis (w : Fin d → ℂ) (a : Fin d) : pairing β w (β a) = w a := by
  simp [pairing, Finsupp.single_apply]

def torusHom (w : Fin d → ℂ) : Multiplicative X →* Γ((𝟙_ (Over (Sp ℂ))).left, ⊤)ˣ :=
  MonoidHom.mk' (fun χ => expUnit (pairing β w χ.toAdd)) fun χ χ' => by
    rw [toAdd_mul, pairing_add_right, expUnit_add]

def torusExp (w : Fin d → ℂ) : 𝟙_ (Over (Sp ℂ)) ⟶ splitTorus (Sp ℂ) X :=
  (GlobalTheory.splitTorusPointsEquiv (Sp ℂ) X _).symm (torusHom β w)

theorem torusExp_add (z w : Fin d → ℂ) : torusExp β (z + w) = torusExp β z * torusExp β w := by
  rw [torusExp, torusExp, torusExp, ← map_mul]
  congr 1
  ext χ
  show (expUnit _).val = (expUnit _ * expUnit _).val
  rw [pairing_add_left, expUnit_add]

theorem monoidHom_ext_basis {U : Type} [CommGroup U] {f f' : Multiplicative X →* U}
    (h : ∀ a, f (Multiplicative.ofAdd (β a)) = f' (Multiplicative.ofAdd (β a))) : f = f' := by
  have e : ∀ (φ : Multiplicative X →* U) (χ : X),
      φ (Multiplicative.ofAdd χ) = ∏ a, φ (Multiplicative.ofAdd (β a)) ^ (β.repr χ a) := fun φ χ => by
    conv_lhs => rw [← β.sum_repr χ]
    rw [ofAdd_sum, map_prod]
    exact Finset.prod_congr rfl fun a _ => by rw [ofAdd_zsmul, map_zpow]
  refine MonoidHom.ext fun χ => ?_
  exact (e f χ.toAdd).trans ((Finset.prod_congr rfl fun a _ => by rw [h a]).trans (e f' χ.toAdd).symm)

theorem torusExp_surjective : Function.Surjective (torusExp (X := X) β) := fun s => by
  let u := GlobalTheory.splitTorusPointsEquiv (Sp ℂ) X (𝟙_ (Over (Sp ℂ))) s
  let w : Fin d → ℂ := fun a => Complex.log (gammaEquiv (u (Multiplicative.ofAdd (β a))).val)
  refine ⟨w, ?_⟩
  have : torusHom β w = u := monoidHom_ext_basis β fun a => by
    refine expUnit_ext ?_
    show gammaEquiv (expUnit _).val = _
    rw [gamma_expUnit, toAdd_ofAdd, pairing_basis]
    refine Complex.exp_log ?_
    exact (((u (Multiplicative.ofAdd (β a))).isUnit).map gammaEquiv).ne_zero
  rw [torusExp, this]
  exact (GlobalTheory.splitTorusPointsEquiv (Sp ℂ) X _).symm_apply_apply s

theorem torusExp_period (a : Fin d) : torusExp (X := X) β (Pi.single a (2 * Real.pi * Complex.I)) = 1 := by
  have : torusHom (X := X) β (Pi.single a (2 * Real.pi * Complex.I)) = 1 := by
    refine MonoidHom.ext fun χ => expUnit_eq_one ?_
    have e : pairing β (Pi.single a (2 * Real.pi * Complex.I)) χ.toAdd =
        ((β.repr χ.toAdd a : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      simp [pairing, Pi.single_apply]
    rw [e]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [torusExp, this, map_one]

theorem valAt'_torusFst (t : 𝟙_ (Over (Sp ℂ)) ⟶ splitTorus (Sp ℂ) X) (α : torusRing ZU X) :
    valAt' (t.left ≫ Rosenlicht.torusFst (Sp ℂ) X) ⊤ ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom α) =
      gammaEquiv ((Rosenlicht.coord t).hom α) := by
  rw [valAt'_eq_valR, valR_eq _ _ (le_preimage_top _)]
  have h3 : (t.left ≫ Rosenlicht.torusFst (Sp ℂ) X).appLE ⊤ ⊤ (le_preimage_top _) =
      (t.left ≫ Rosenlicht.torusFst (Sp ℂ) X).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  simp only [valMap, h3]
  rfl

theorem valAt'_torusFst' (t : 𝟙_ (Over (Sp ℂ)) ⟶ splitTorus (Sp ℂ) X) (α : torusRing ZU X) :
    valAt' (t.left ≫ pullback.fst (splitTorusAff ZU X).hom (toZ (Sp ℂ))) ⊤
      ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom α) = gammaEquiv ((Rosenlicht.coord t).hom α) :=
  valAt'_torusFst t α

theorem torusExp_hol_char (w : Fin d → ℂ) (χ : X) : gammaEquiv ((Rosenlicht.coord (torusExp β w)).hom (AddMonoidAlgebra.single χ 1)) = Complex.exp (pairing β w χ) := by
  have e : GlobalTheory.SplitTorusPoints.toHom (torusExp β w) = torusHom β w :=
    (GlobalTheory.splitTorusPointsEquiv (Sp ℂ) X _).apply_symm_apply _
  rw [← GlobalTheory.SplitTorusPoints.toHom_val, e]
  exact gamma_expUnit _

theorem differentiable_pairing (χ : X) : Differentiable ℂ (fun w : Fin d → ℂ => pairing β w χ) := by
  unfold pairing
  fun_prop

theorem differentiable_torusExp_coord (α : torusRing ZU X) :
    Differentiable ℂ (fun w : Fin d → ℂ => gammaEquiv ((Rosenlicht.coord (torusExp β w)).hom α)) := by
  induction α using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f f' hf hf' =>
    simp only [map_add]
    exact hf.add hf'
  | single χ r =>
    have e : (AddMonoidAlgebra.single χ r : AddMonoidAlgebra (ULift.{0} ℤ) X) =
        r.down • AddMonoidAlgebra.single χ 1 := by
      rw [AddMonoidAlgebra.smul_single]
      congr 1
      ext
      simp
    have e' : ∀ w : Fin d → ℂ, gammaEquiv ((Rosenlicht.coord (torusExp β w)).hom (AddMonoidAlgebra.single χ r)) =
        r.down • Complex.exp (pairing β w χ) := fun w => by
      rw [← torusExp_hol_char, e, map_zsmul, map_zsmul]
    simp only [e']
    exact ((differentiable_pairing β χ).cexp).const_smul _

theorem isHolTo_torusExp : IsHolTo Set.univ (fun w => (torusExp (X := X) β w).left) := by
  have h1 : IsHolTo Set.univ (fun w => (torusExp (X := X) β w).left ≫ Rosenlicht.torusFst (Sp ℂ) X) := by
    refine ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_of_affine (T := Spec (torusRing ZU X)) isOpen_univ fun r => ?_
    obtain ⟨α, rfl⟩ : ∃ α, r = (Scheme.ΓSpecIso (torusRing ZU X)).inv.hom α :=
      ⟨(Scheme.ΓSpecIso (torusRing ZU X)).hom.hom r, by simp⟩
    simp only [valAt'_torusFst]
    exact (differentiable_torusExp_coord β α).differentiableOn.congr fun w _ => valAt'_torusFst _ α
  have h2 : IsHolTo (V := Fin d → ℂ) Set.univ (fun _ => 𝟙 (Sp ℂ)) :=
    fun U f => ⟨by simp only [Set.mem_univ, true_and]; exact isOpen_const, differentiableOn_const _⟩
  exact GlobalTheory.HolPullback.isHolTo_of_components (Fin d → ℂ) Set.univ _ _ _ _ (pullback.fst _ _) (pullback.snd _ _) _ _ _
    (IsPullback.of_hasPullback (splitTorusAff ZU X).hom (toZ (Sp ℂ))) isOpen_univ h1
    (by
      convert h2 using 2 with w
      exact Over.w (torusExp (X := X) β w))

theorem exists_torusExp (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] :
    ∃ (d : ℕ) (t : (Fin d → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ splitTorus (Sp ℂ) X)),
      (∀ z w, t (z + w) = t z * t w) ∧ IsHolTo Set.univ (fun z => (t z).left) ∧ Function.Surjective t ∧
      ∀ a : Fin d, t (Pi.single a (2 * Real.pi * Complex.I)) = 1 :=
  ⟨_, torusExp (Module.finBasis ℤ X), torusExp_add _, isHolTo_torusExp _, torusExp_surjective _, torusExp_period _⟩

end TorusExp

end GlobalTheory.CompanionTheory.Ar.Flat.PerSpan

namespace GlobalTheory.CompanionTheory.Ar.Flat

open PerSpan

theorem span_per_eq_top : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ)
    (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ))
    (e : FamExp G M B ψ), IsSemiAbelian G → ∀ b ∈ B, Submodule.span ℂ (e.per b) = ⊤ := by
  intro R _ G _ _ g n M B ψ e hG b hb
  obtain ⟨T⟩ := hG.fibres ℂ (spMap (ψ b))
  have hsurj := GlobalTheory.T.exponential_surjective_semiabelian R G g n M B ψ e hG b hb
  have hq := T.q_hom
  have hi := T.i_hom
  letI := T.addCommGroup
  letI := T.grpB
  have := T.free
  have := T.finite
  have := hG.smooth
  have := T.q_quasiCompact
  have := T.q_surjective
  have hlft : LocallyOfFiniteType T.q.left := by
    have : LocallyOfFiniteType (T.q.left ≫ T.B.hom) := by
      rw [Over.w]
      show LocallyOfFiniteType (pullback.snd G.hom (spMap (ψ b)))
      infer_instance
    exact locallyOfFiniteType_of_comp _ T.B.hom
  obtain ⟨d, t, tadd, thol, tsurj, tper⟩ := exists_torusExp T.X
  have := (compact_alt_alt T.B T.isAbelian).1
  have := (compact_alt_alt T.B T.isAbelian).2
  have := isTopologicalGroup_over (C := ℂ) T.B
  let x := spMap (ψ b)
  let u : (Fin d → ℂ) → (Over.mk x ⟶ G) := fun w => ofFibre G x (t w ≫ T.i)
  have uadd : ∀ z w, u (z + w) = u z * u w := fun z w => by
    simp only [u, tadd, MonObj.mul_comp, ofFibre_mul]
  have uhol : IsHolTo Set.univ (fun z => (u z).left) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp thol (T.i.left ≫ pullback.fst G.hom x)
  obtain ⟨h, hh⟩ := exists_linear_lift_at_point R G g n M B ψ e b hb d u uadd uhol
  have hW : ∀ a, h (Pi.single a (2 * Real.pi * Complex.I)) ∈ Submodule.span ℂ (e.per b) := fun a => by
    refine Submodule.subset_span ?_
    show e.ex b _ = 1
    rw [hh]
    simp only [u, tper, MonObj.one_comp, ofFibre_one]
  have hW' : ∀ w, h w ∈ Submodule.span ℂ (e.per b) := fun w => by
    have e1 : w = ∑ a, (w a / (2 * Real.pi * Complex.I)) • (Pi.single a (2 * Real.pi * Complex.I) : Fin d → ℂ) := by
      ext c
      have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
      simp [Finset.sum_apply, Pi.single_apply, h2]
    rw [e1, map_sum]
    exact Submodule.sum_mem _ fun a _ => by
      rw [map_smul]
      exact Submodule.smul_mem _ _ (hW a)
  let π : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ T.B) := fun z => toFibre G x (e.ex b z) ≫ T.q
  refine eq_top_of_compact_quotient g _ π (fun z w => ?_) ?_ (fun y => ?_) _ (fun z hz => ?_)
  · simp only [π, e.add b hb, toFibre_mul, MonObj.mul_comp]
  · refine (continuous_over_comp T.q).comp ?_
    refine (isEmbedding_left _).continuous_iff.2 ?_
    refine (isEmbedding_of_isPullback (C := ℂ) (IsPullback.of_hasPullback G.hom x)).continuous_iff.2 ?_
    refine Continuous.prodMk ?_ ?_
    · have := isHolTo_ex_slice e hb
      refine (continuous_of_differentiableOn (fun U f => ?_)).congr fun z => (pullback.lift_fst _ _ _).symm
      simpa using this U f
    · exact continuous_const.congr fun z => (pullback.lift_snd _ _ _).symm
  · obtain ⟨p, hp⟩ := GlobalTheory.SS.SemiDivisible.exists_lift_point T.q y
    obtain ⟨z, hz⟩ := hsurj (ofFibre G x p)
    refine ⟨z, ?_⟩
    simp only [π, hz, toFibre_ofFibre, hp]
  · have hk : toFibre G x (e.ex b z) ≫ T.q = toUnit _ ≫ η[T.B] := hz
    let s := T.isKernel.lift (toFibre G x (e.ex b z)) (toUnit _) hk
    have hs : s ≫ T.i = toFibre G x (e.ex b z) := T.isKernel.lift_fst _ _ _
    obtain ⟨w, hw⟩ := tsurj s
    have h1 : e.ex b (h w) = e.ex b z := by
      rw [hh]
      simp only [u, hw, hs, ofFibre_toFibre]
    have h2 : z - h w ∈ e.per b := by
      show e.ex b _ = 1
      have := e.add b hb (z - h w) (h w)
      rw [sub_add_cancel, h1] at this
      exact right_eq_mul.1 this
    have := Submodule.add_mem _ (Submodule.subset_span h2) (hW' w)
    rwa [sub_add_cancel] at this

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_lattice_spans : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp G M B ψ), IsSemiAbelian G → ∀ b ∈ B, Submodule.span ℂ (e.per b) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.span_per_eq_top | exact GlobalTheory.CompanionTheory.Ar.Flat.span_per_eq_top | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.span_per_eq_top <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_periodQuot_transport {V P : Type} [AddCommGroup V] [Module ℂ V] [CommGroup P] (E : V → P)
    (hadd : ∀ z w, E (z + w) = E z * E w) (hsurj : Function.Surjective E) (Γ₀ : Submodule ℤ V)
    (hΓ : (Γ₀ : Set V) = {z | E z = 1}) (N : ℕ) (hN : 0 < N) (T₀ : Set P) (hT₀ : ∀ τ ∈ T₀, τ ^ N = 1) :
    ∃ T : Set (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))),
      Nat.card (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))) = Nat.card {p : P // p ^ N = 1} ∧
      Nat.card T = Nat.card T₀ ∧
      (∀ x : Γ₀, Submodule.Quotient.mk x ∈ T → E ((N : ℂ)⁻¹ • (x : V)) ∈ T₀) ∧
      ∀ x : Γ₀, E ((N : ℂ)⁻¹ • (x : V)) ^ N = 1 := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hmem : ∀ z : V, z ∈ Γ₀ ↔ E z = 1 := fun z => by
    have := Set.ext_iff.1 hΓ z
    simpa using this
  have h0 : E 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hpow : ∀ (k : ℕ) (z : V), E ((k : ℂ) • z) = E z ^ k := by
    intro k z
    induction k with
    | zero => simp [h0]
    | succ k ih => rw [Nat.cast_succ, add_smul, one_smul, hadd, ih, pow_succ]
  have hdiv : ∀ z : V, (N : ℂ) • (N : ℂ)⁻¹ • z = z := fun z => by rw [smul_smul, mul_inv_cancel₀ hNc, one_smul]
  let Eh : V →+ Additive P := AddMonoidHom.mk' (fun z => Additive.ofMul (E z)) (fun a b => by
    rw [hadd]; rfl)
  let d : Γ₀ →+ V := (((N : ℂ)⁻¹ • (LinearMap.id : V →ₗ[ℂ] V)).toAddMonoidHom).comp Γ₀.subtype.toAddMonoidHom
  let f : Γ₀ →ₗ[ℤ] Additive P := (Eh.comp d).toIntLinearMap
  have hf : ∀ x : Γ₀, f x = Additive.ofMul (E ((N : ℂ)⁻¹ • (x : V))) := fun x => rfl
  have hle : LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀)) ≤ LinearMap.ker f := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, hf]
    have : (N : ℂ)⁻¹ • (((((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀)) y : Γ₀)) : V) = y := by
      have : ((((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀)) y : Γ₀) : V) = (N : ℂ) • (y : V) := by
        simp [Nat.cast_smul_eq_nsmul]
      rw [this, smul_smul, inv_mul_cancel₀ hNc, one_smul]
    rw [this, (hmem _).1 y.2]
    rfl
  let φ := Submodule.liftQ _ f hle
  have hφ : ∀ x : Γ₀, φ (Submodule.Quotient.mk x) = Additive.ofMul (E ((N : ℂ)⁻¹ • (x : V))) := fun x => rfl
  have hφN : ∀ q, (Additive.toMul (φ q)) ^ N = 1 := by
    intro q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [hφ, toMul_ofMul, ← hpow, hdiv]
    exact (hmem _).1 x.2
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [hφ] at hq
    have h1 : E ((N : ℂ)⁻¹ • (x : V)) = 1 := hq
    have h2 : (N : ℂ)⁻¹ • (x : V) ∈ Γ₀ := (hmem _).2 h1
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨⟨_, h2⟩, Subtype.ext ?_⟩
    have : ((((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀)) ⟨_, h2⟩ : Γ₀) : V) = (N : ℂ) • (N : ℂ)⁻¹ • (x : V) := by
      simp [Nat.cast_smul_eq_nsmul]
    rw [this, hdiv]
  have hrange : ∀ p : P, p ^ N = 1 → ∃ q, Additive.toMul (φ q) = p := by
    intro p hp
    obtain ⟨z, rfl⟩ := hsurj p
    have h1 : (N : ℂ) • z ∈ Γ₀ := (hmem _).2 (by rw [hpow, hp])
    refine ⟨Submodule.Quotient.mk ⟨_, h1⟩, ?_⟩
    rw [hφ, toMul_ofMul]
    congr 1
    change (N : ℂ)⁻¹ • (N : ℂ) • z = z
    rw [smul_smul, inv_mul_cancel₀ hNc, one_smul]
  let ψ : (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))) → P := fun q => Additive.toMul (φ q)
  have hψ : Function.Injective ψ := fun a b h => hinj (Additive.toMul.injective h)
  refine ⟨ψ ⁻¹' T₀, ?_, ?_, ?_, fun x => hφN (Submodule.Quotient.mk x)⟩
  · refine Nat.card_congr (Equiv.ofBijective (fun q => ⟨ψ q, hφN q⟩) ⟨?_, ?_⟩)
    · exact fun a b h => hψ (congrArg Subtype.val h)
    · rintro ⟨p, hp⟩
      obtain ⟨q, hq⟩ := hrange p hp
      exact ⟨q, Subtype.ext hq⟩
  · refine Nat.card_congr (Equiv.ofBijective (fun q => ⟨ψ q.1, q.2⟩) ⟨?_, ?_⟩)
    · exact fun a b h => Subtype.ext (hψ (congrArg Subtype.val h))
    · rintro ⟨p, hp⟩
      obtain ⟨q, hq⟩ := hrange p (hT₀ p hp)
      refine ⟨⟨q, ?_⟩, Subtype.ext hq⟩
      change ψ q ∈ T₀
      rw [show ψ q = p from hq]
      exact hp
  · intro x hx
    exact hx

theorem toric_torsion_radical_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp t.G M B ψ), SmoothOfRelativeDimension g t.G.hom → ∀ b₀ ∈ B, ∀ Γ₀ : Submodule ℤ (Fin g → ℂ), (Γ₀ : Set (Fin g → ℂ)) = e.per b₀ → ∀ N : ℕ, 0 < N → ∃ T : Set (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))), Nat.card (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))) * Nat.card T = N ^ (2 * g) ∧ ∀ x y : Γ₀, Submodule.Quotient.mk x ∈ T → GlobalTheory.UU.CubWeil t.cub N (e.ex b₀ ((N : ℂ)⁻¹ • (x : Fin g → ℂ))) (e.ex b₀ ((N : ℂ)⁻¹ • (y : Fin g → ℂ))) 1 := by
  intro E _ _ _ H R _ t g n M B ψ e dG b₀ hb₀ Γ₀ hΓ N hN
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨T₀, hT₁, hT₂, hT₃⟩ := GlobalTheory.exists_toric_torsion_cubWeil_one GlobalTheory.firstFiveLaws.2.2.1 (Sp R) t.G t.semi t.PP t.cub g N ℂ
    (spMap (ψ b₀)) dG hNc
  have hsurj := GlobalTheory.T.exponential_surjective_semiabelian R t.G g n M B ψ e t.semi b₀ hb₀
  obtain ⟨T, h₁, h₂, h₃, h₄⟩ := exists_periodQuot_transport (e.ex b₀) (e.add b₀ hb₀) hsurj Γ₀ hΓ N hN T₀ hT₁
  refine ⟨T, by rw [h₁, h₂, hT₃], fun x y hx => ?_⟩
  exact hT₂ _ (h₃ x hx) _ (h₄ y)

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_periods_finite_quotient : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp t.G M B ψ), SmoothOfRelativeDimension g t.G.hom → ∀ b₀ ∈ B, ∀ Γ₀ : Submodule ℤ (Fin g → ℂ), (Γ₀ : Set (Fin g → ℂ)) = e.per b₀ → ∀ N : ℕ, 0 < N → ∃ T : Set (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))), Nat.card (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))) * Nat.card T = N ^ (2 * g) ∧ ∀ x y : Γ₀, Submodule.Quotient.mk x ∈ T → GlobalTheory.UU.CubWeil t.cub N (e.ex b₀ ((N : ℂ)⁻¹ • (x : Fin g → ℂ))) (e.ex b₀ ((N : ℂ)⁻¹ • (y : Fin g → ℂ))) 1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.toric_torsion_radical_period
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.Link

open GroundTheory.Heights₂.Heights.Regular

section Hol

variable {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V'] [NormedSpace ℂ V']

theorem isHolTo_pull {X : Scheme.{0}} {B : Set V} {y : V → (Sp ℂ ⟶ X)} (hy : IsHolTo B y)
    {W : Set V'} (hW : IsOpen W) {φ : V' → V} (hφ : DifferentiableOn ℂ φ W) (hm : Set.MapsTo φ W B) :
    IsHolTo W (fun w => y (φ w)) := by
  intro U f
  have hset : {w ∈ W | ⊤ ≤ y (φ w) ⁻¹ᵁ U} = W ∩ φ ⁻¹' {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} := by
    ext w
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, hm h1, h2⟩
    · rintro ⟨h1, -, h2⟩
      exact ⟨h1, h2⟩
  refine ⟨by rw [hset]; exact hφ.continuousOn.isOpen_inter_preimage hW (hy U f).1, ?_⟩
  refine DifferentiableOn.comp (g := fun b => valAt' (y b) U f) (t := {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U})
    (hy U f).2 (hφ.mono fun w hw => hw.1) ?_
  intro w hw
  exact ⟨hm hw.1, hw.2⟩

end Hol

section Fam

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {g n : ℕ}
  {M : LieModel G (𝟙 (Sp R)) (Fin g → R)} {B B' : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}

def restrict (e : FamExp G M B ψ) (hB' : IsOpen B') (h : B' ⊆ B) : FamExp G M B' ψ where
  ex := e.ex
  add b hb := e.add b (h hb)
  hol := isHolTo_pull e.hol (hB'.prod isOpen_univ) differentiableOn_id fun p hp => ⟨h hp.1, hp.2⟩
  diff b hb := e.diff b (h hb)
  log b hb := e.log b (h hb)

theorem ex_zero (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) : e.ex b 0 = 1 := by
  have h := e.add b hb 0 0
  rw [add_zero] at h
  exact (left_eq_mul.mp h)

theorem ex_nsmul (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) (y : Fin g → ℂ) (k : ℕ) :
    e.ex b ((k : ℂ) • y) = e.ex b y ^ k := by
  induction k with
  | zero => simpa using ex_zero e hb
  | succ k ih => rw [Nat.cast_succ, add_smul, _root_.one_smul, e.add b hb, ih, pow_succ]

def perGrp (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) : AddSubgroup (Fin g → ℂ) where
  carrier := e.per b
  zero_mem' := ex_zero e hb
  add_mem' := by
    intro x y hx hy
    have hx' : e.ex b x = 1 := hx
    have hy' : e.ex b y = 1 := hy
    show e.ex b (x + y) = 1
    rw [e.add b hb, hx', hy', _root_.one_mul]
  neg_mem' := by
    intro x hx
    have hx' : e.ex b x = 1 := hx
    show e.ex b (-x) = 1
    have h := e.add b hb (-x) x
    rw [neg_add_cancel, ex_zero e hb, hx', _root_.mul_one] at h
    exact h.symm

theorem mem_closure_per (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) (p : Fin g → ℂ) :
    p ∈ AddSubgroup.closure (e.per b) ↔ p ∈ e.per b := by
  have h : AddSubgroup.closure (e.per b) = perGrp e hb := by
    have h' : e.per b = ((perGrp e hb : AddSubgroup (Fin g → ℂ)) : Set (Fin g → ℂ)) := rfl
    rw [h', AddSubgroup.closure_eq]
  rw [h]
  rfl

end Fam

section Geo

variable {n a : ℕ}

theorem smul_mem_punct {ρ : ℝ} (hρ : 0 < ρ) {z : Fin n → ℂ} :
    (ρ : ℂ) • z ∈ punct n a ρ ↔ z ∈ punct n a 1 := by
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hn : ‖(ρ : ℂ) • z‖ = ρ * ‖z‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
  simp only [punct, Set.mem_setOf_eq, mem_ball_zero_iff, hn, Pi.smul_apply, smul_eq_mul, ne_eq,
    mul_eq_zero, hρ', false_or]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith, h2⟩

theorem smul_mem_ball {ρ : ℝ} (hρ : 0 < ρ) {z : Fin n → ℂ} (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) :
    (ρ : ℂ) • z ∈ Metric.ball (0 : Fin n → ℂ) ρ := by
  have hn : ‖(ρ : ℂ) • z‖ = ρ * ‖z‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
  rw [mem_ball_zero_iff] at hz ⊢
  rw [hn]
  nlinarith

theorem punct_subset_ball {ρ : ℝ} : punct n a ρ ⊆ Metric.ball (0 : Fin n → ℂ) ρ := fun _ h => h.1

theorem expCover_mem_punct (h : a ≤ n) {w : Fin n → ℂ} (hw : w ∈ logCover h) :
    expCover a w ∈ punct n a 1 := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos]
    intro k
    by_cases hk : k.val < a
    · have hre := hw.1 ⟨k.val, hk⟩
      have hcast : Fin.castLE h ⟨k.val, hk⟩ = k := Fin.ext rfl
      rw [hcast] at hre
      simp only [expCover, if_pos hk]
      rw [Complex.norm_exp]
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.2 hre
    · simp only [expCover, if_neg hk]
      exact hw.2 k (not_lt.mp hk)
  · simp only [expCover, if_pos hi]
    exact Complex.exp_ne_zero _

theorem exists_seq_punct : ∃ u : ℕ → (Fin n → ℂ), Tendsto u atTop (𝓝 0) ∧ ∀ k, u k ∈ punct n a 1 := by
  let c : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) / 2
  have hc0 : ∀ k, 0 < c k := fun k => by positivity
  have hc1 : ∀ k, c k < 1 := fun k => by
    have h1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have : c k = 1 / ((k : ℝ) + 1) / 2 := rfl
    linarith
  have hct : Tendsto c atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2
    rw [zero_div] at h
    exact h
  refine ⟨fun k _ => (c k : ℂ), ?_, fun k => ⟨?_, fun i _ => ?_⟩⟩
  · rw [tendsto_pi_nhds]
    intro i
    have h := (Complex.continuous_ofReal.tendsto 0).comp hct
    rw [Complex.ofReal_zero] at h
    exact h
  · rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos]
    intro i
    rw [Complex.norm_real, Real.norm_of_nonneg (hc0 k).le]
    exact hc1 k
  · show ((c k : ℝ) : ℂ) ≠ 0
    exact_mod_cast (hc0 k).ne'

end Geo

theorem exists_radius_le {I : Type} (s : Finset I) (c : ℝ) (hc : 0 < c) (f : I → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ c ∧ ∀ i ∈ s, ρ ≤ f i :=
  _root_.UpperTheory.Reformulated.B.Ydd5.main s c hc f hf

theorem exists_additive_sections {n g : ℕ} (Γ₀ : Submodule ℤ (Fin g → ℂ)) [Module.Free ℤ Γ₀] [Module.Finite ℤ Γ₀]
    (Q : (Fin n → ℂ) → AddSubgroup (Fin g → ℂ)) (c : ℝ) (hc : 0 < c)
    (hsp : ∀ x : Γ₀, ∃ (ε : ℝ) (s : (Fin n → ℂ) → (Fin g → ℂ)), 0 < ε ∧
      DifferentiableOn ℂ s (Metric.ball 0 ε) ∧ s 0 = x ∧ ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ε, s b ∈ Q b) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ c ∧ ∃ S : Γ₀ → (Fin n → ℂ) → (Fin g → ℂ),
      (∀ x, DifferentiableOn ℂ (S x) (Metric.ball 0 ρ)) ∧ (∀ x, S x 0 = x) ∧
      (∀ x y b, S (x + y) b = S x b + S y b) ∧ ∀ x, ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, S x b ∈ Q b := by
  classical
  let bs := Module.Free.chooseBasis ℤ Γ₀
  choose εs ss hε hd h0 hq using fun j => hsp (bs j)
  obtain ⟨ρ, hρ0, hρc, hρ⟩ := exists_radius_le Finset.univ c hc εs hε
  have hsub : ∀ j, Metric.ball (0 : Fin n → ℂ) ρ ⊆ Metric.ball 0 (εs j) := fun j =>
    Metric.ball_subset_ball (hρ j (Finset.mem_univ j))
  refine ⟨ρ, hρ0, hρc, fun x b => ∑ j, ((bs.repr x j : ℤ) : ℂ) • ss j b, ?_, ?_, ?_, ?_⟩
  · intro x
    exact DifferentiableOn.fun_sum fun j _ => ((hd j).mono (hsub j)).fun_const_smul _
  · intro x
    have hx : (x : Fin g → ℂ) = ∑ j, (bs.repr x j) • ((bs j : Γ₀) : Fin g → ℂ) := by
      have h := congrArg Γ₀.subtype (bs.sum_repr x)
      rw [map_sum] at h
      simp only [map_smul, Submodule.subtype_apply] at h
      exact h.symm
    simp only [h0]
    rw [hx]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Int.cast_smul_eq_zsmul ℂ _ _
  · intro x y b
    simp only [map_add, Finsupp.add_apply, Int.cast_add, add_smul, Finset.sum_add_distrib]
  · intro x b hb
    refine sum_mem fun j _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    exact zsmul_mem (hq j b (hsub j hb)) _

section Carry

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem cubWeil_carry {R : Type} [CommRing R] {t : SAB H (Sp R)} {g n : ℕ} {M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)}
    {ρ : ℝ} {ψ : (Fin n → ℂ) → (R →+* ℂ)} (e : FamExp t.G M (Metric.ball 0 ρ) ψ) (hρ : 0 < ρ) (N : ℕ) (hN : 0 < N)
    (s s' : (Fin n → ℂ) → (Fin g → ℂ)) (hs : DifferentiableOn ℂ s (Metric.ball 0 ρ))
    (hs' : DifferentiableOn ℂ s' (Metric.ball 0 ρ)) (hp : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, s b ∈ e.per b)
    (hp' : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, s' b ∈ e.per b) (ζ : ℂˣ)
    (h0 : GlobalTheory.UU.CubWeil t.cub N (e.ex 0 ((N : ℂ)⁻¹ • s 0)) (e.ex 0 ((N : ℂ)⁻¹ • s' 0)) (unitOn ζ)) :
    ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ,
      GlobalTheory.UU.CubWeil t.cub N (e.ex b ((N : ℂ)⁻¹ • s b)) (e.ex b ((N : ℂ)⁻¹ • s' b)) (unitOn ζ) := by
  have hhol : ∀ u : (Fin n → ℂ) → (Fin g → ℂ), DifferentiableOn ℂ u (Metric.ball 0 ρ) →
      IsHolTo (Metric.ball 0 ρ) (fun b => (e.ex b ((N : ℂ)⁻¹ • u b)).left) := fun u hu =>
    isHolTo_pull (φ := fun b => (b, (N : ℂ)⁻¹ • u b)) e.hol Metric.isOpen_ball
      (differentiableOn_id.prodMk (hu.fun_const_smul _)) (fun b hb => ⟨hb, trivial⟩)
  have htor : ∀ u : (Fin n → ℂ) → (Fin g → ℂ), (∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, u b ∈ e.per b) →
      ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, e.ex b ((N : ℂ)⁻¹ • u b) ^ N = 1 := fun u hu b hb => by
    have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    rw [← ex_nsmul e hb, smul_smul, mul_inv_cancel₀ hNc, _root_.one_smul]
    exact hu b hb
  exact GlobalTheory.T.torsion_section_eq_of_connected (Sp R) t.G t.PP t.cub n N (Metric.ball 0 ρ) (fun b => spMap (ψ b))
    (fun b => e.ex b ((N : ℂ)⁻¹ • s b)) (fun b => e.ex b ((N : ℂ)⁻¹ • s' b)) ζ 0 hN Metric.isOpen_ball
    (convex_ball _ _).isPreconnected (Metric.mem_ball_self hρ) (hhol s hs) (hhol s' hs')
    (fun b hb => ⟨htor s hp b hb, htor s' hp' b hb, (Over.w _).trans (Over.w _).symm⟩) h0

end Carry

theorem exists_int_of_exp_eq_one {r : ℝ} {N : ℕ} (hN : 0 < N)
    (h : ((1 : ℂˣ) : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (r : ℂ) / N)) :
    ∃ k : ℤ, r = N * k := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 (by simpa using h.symm)
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  rw [div_eq_iff hNc] at hm
  have h4 : (2 * Real.pi * Complex.I : ℂ) * ((r : ℂ) + N * m) = 0 := by linear_combination -hm
  have h5 : (r : ℂ) + N * m = 0 := (mul_eq_zero.1 h4).resolve_left hc
  refine ⟨-m, ?_⟩
  have h6 : (r : ℂ) = ((N * (-m : ℤ) : ℝ) : ℂ) := by
    push_cast
    linear_combination h5
  exact_mod_cast h6

theorem exists_logPeriods_famExp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → ∃ (ρ : ℝ) (Λ : Type) (_ : AddCommGroup Λ) (L : Flat.LogPeriods n a C.g Λ) (e : Flat.FamExp C.t.G C.M (Metric.ball 0 ρ) C.ψ), 0 < ρ ∧ ρ ≤ 1 ∧ (∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, (∀ p, p ∈ e.per ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ↔ ∃ x, L.P w x = p) ∧ ∀ (N : ℕ) (ζ : ℂˣ) (x x' : Λ), 0 < N → GlobalTheory.UU.CubWeil C.t.cub N (e.ex ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ((N : ℂ)⁻¹ • L.P w x)) (e.ex ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ((N : ℂ)⁻¹ • L.P w x')) (unitOn ζ) → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((L.E x x' : ℤ) : ℂ) / N)) := by
  intro E _ _ _ H D l Xo σ n a C hpq hσ
  obtain ⟨g', ty, hty⟩ := GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q
  obtain ⟨FU⟩ := GlobalTheory.familyUnif_of_laws GlobalTheory.abelianSchemeLaws_all.1 E H D l Xo σ g' ty hpq hσ hty
  have hsemi : IsSemiAbelian C.t.G := C.t.semi
  obtain ⟨ε, hε, hεB, ⟨e₀⟩⟩ := GlobalTheory.T.exists_family_exponential_locally C.R C.t.G C.g n C.M (Metric.ball 0 1) C.ψ hsemi.smooth C.hol 0
    (Metric.mem_ball_self one_pos)
  have h0ε : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) ε := Metric.mem_ball_self hε
  obtain ⟨Γ₀, hΓ₀, -, hfin, hfree⟩ := GlobalTheory.T.period_lattice_discrete_free C.R C.t.G C.g n C.M _ C.ψ e₀ 0 h0ε
  let Q : (Fin n → ℂ) → AddSubgroup (Fin C.g → ℂ) := fun b => AddSubgroup.closure (e₀.per b)
  have hQ : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ε, ∀ p, p ∈ Q b ↔ p ∈ e₀.per b := fun b hb p =>
    mem_closure_per e₀ hb p
  have hsp : ∀ x : Γ₀, ∃ (ε' : ℝ) (s : (Fin n → ℂ) → (Fin C.g → ℂ)), 0 < ε' ∧
      DifferentiableOn ℂ s (Metric.ball 0 ε') ∧ s 0 = x ∧ ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ε', s b ∈ Q b := by
    intro x
    obtain ⟨ε', s, h0, hsub, hd, hs0, hs⟩ := GlobalTheory.T.period_holomorphic_continuation C.R C.t.G C.g n C.M _ C.ψ e₀ Metric.isOpen_ball 0 h0ε x
      (by rw [← hΓ₀]; exact x.2)
    exact ⟨ε', s, h0, hd, hs0, fun b hb => (hQ b (hsub hb) _).2 (hs b hb)⟩
  obtain ⟨ρ, hρ0, hρc, S, hSd, hS0, hSa, hSq⟩ := exists_additive_sections Γ₀ Q (min 1 ε) (lt_min one_pos hε) hsp
  have hρ1 : ρ ≤ 1 := hρc.trans (min_le_left _ _)
  have hball : Metric.ball (0 : Fin n → ℂ) ρ ⊆ Metric.ball 0 ε :=
    Metric.ball_subset_ball (hρc.trans (min_le_right _ _))
  have hball1 : Metric.ball (0 : Fin n → ℂ) ρ ⊆ Metric.ball 0 1 := Metric.ball_subset_ball hρ1
  have h0ρ : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) ρ := Metric.mem_ball_self hρ0
  let e : FamExp C.t.G C.M (Metric.ball 0 ρ) C.ψ := restrict e₀ Metric.isOpen_ball hball
  have hQ' : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ p, p ∈ Q b ↔ p ∈ e.per b := fun b hb p => hQ b (hball hb) p
  have hΓ₀' : (Γ₀ : Set (Fin C.g → ℂ)) = e.per 0 := hΓ₀
  have hSp : ∀ x, ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, S x b ∈ e.per b := fun x b hb =>
    (hQ' b hb _).1 (hSq x b hb)
  obtain ⟨i, Hf, hrank, hopen, hloc⟩ := GlobalTheory.T.boundary_chart_hodge_matrix E H D l Xo σ n a C g' ty FU ρ e hρ0 hρ1
  obtain ⟨hfreeL, hfinL, -⟩ := GlobalTheory.Coisotropic.lattice_rank E H (FU.Di i)
  have hU : ∀ z ∈ punct n a 1, (ρ : ℂ) • z ∈ punct n a ρ := fun z hz => (smul_mem_punct hρ0).2 hz
  have hsm : Differentiable ℂ (fun z : Fin n → ℂ => (ρ : ℂ) • z) := differentiable_id.fun_const_smul _
  have key : ∃ L : Flat.LogPeriods n a C.g (FU.Di i).La, L.H = (fun z => Hf ((ρ : ℂ) • z)) ∧
      ∀ w ∈ logCover L.a_le, (L.P w).range = Q ((ρ : ℂ) • expCover a w) := by
    refine GlobalTheory.T.period_lattice_on_punctured_disc n a C.g C.a_le (FU.Di i).La (FU.Di i).EF (fun z => Q ((ρ : ℂ) • z))
      (fun z => Hf ((ρ : ℂ) • z)) (punct n a 1) Γ₀ (fun x z => S x ((ρ : ℂ) • z)) rfl hrank (FU.Di i).alt
      (FU.Di i).unimod ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact fun z hz => ⟨(hopen _ (hU z hz)).1, fun x hx => (hopen _ (hU z hz)).2.1 x hx⟩
    · intro z₀ hz₀
      obtain ⟨N, hNo, hzN, hNp, P, hPd, hP⟩ := hloc _ (hU z₀ hz₀)
      refine ⟨(fun z => (ρ : ℂ) • z) ⁻¹' N, hNo.preimage hsm.continuous, hzN,
        fun z hz => (smul_mem_punct hρ0).1 (hNp hz), fun z => P ((ρ : ℂ) • z), fun x => ?_, fun z hz => ?_⟩
      · exact (hPd x).comp hsm.differentiableOn (fun z hz => hz)
      · obtain ⟨h1, h2, h3⟩ := hP _ hz
        refine ⟨h1, ?_, h3⟩
        ext p
        have h4 : p ∈ (P ((ρ : ℂ) • z)).range ↔ p ∈ e.per ((ρ : ℂ) • z) := by
          rw [← SetLike.mem_coe, h2]
        rw [h4]
        exact (hQ' _ (punct_subset_ball (hNp hz)) p).symm
    · intro x
      refine ⟨(hSd x).comp hsm.differentiableOn (fun z hz => smul_mem_ball hρ0 hz), ?_,
        fun z hz => hSq x _ (smul_mem_ball hρ0 hz.1)⟩
      show S x ((ρ : ℂ) • 0) = x
      rw [smul_zero]
      exact hS0 x
    · exact fun x y z => hSa x y _
    · intro s hs hsU
      obtain ⟨u, hu, huU⟩ := exists_seq_punct (n := n) (a := a)
      have hρc' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0.ne'
      have htend : Tendsto (fun k => (ρ : ℂ) • u k) atTop (𝓝 0) := by
        have h := hu.const_smul (ρ : ℂ)
        rwa [smul_zero] at h
      have hcl := GlobalTheory.T.period_set_closed C.R C.t.G C.g n C.M (Metric.ball 0 ρ) C.ψ e hsemi.separated
        ⟨Metric.isOpen_ball, fun r => (C.hol.2 r).mono hball1⟩ 0 h0ρ (fun b => s ((ρ : ℂ)⁻¹ • b))
        (ContinuousAt.comp_of_eq hs (continuous_const_smul _).continuousAt (smul_zero _))
        (htend.frequently (Eventually.frequently (Eventually.of_forall fun k => by
          refine ⟨punct_subset_ball (hU _ (huU k)), ?_⟩
          show s ((ρ : ℂ)⁻¹ • (ρ : ℂ) • u k) ∈ e.per ((ρ : ℂ) • u k)
          rw [smul_smul, inv_mul_cancel₀ hρc', _root_.one_smul]
          exact (hQ' _ (punct_subset_ball (hU _ (huU k))) _).1 (hsU _ (huU k)))))
      have h0 : s 0 ∈ e.per 0 := by simpa using hcl
      rw [← hΓ₀'] at h0
      exact h0
    · rw [hΓ₀']
      exact GlobalTheory.T.period_lattice_spans C.R C.t.G C.g n C.M _ C.ψ e hsemi 0 h0ρ
    · intro N hN
      obtain ⟨T, hT, hTw⟩ := GlobalTheory.T.torsion_periods_finite_quotient E H C.R C.t C.g n C.M (Metric.ball 0 ρ) C.ψ e C.dim 0 h0ρ Γ₀ hΓ₀' N hN
      refine ⟨T, hT, fun x y hx z hz => ?_⟩
      have hb := hU z hz
      have hbm := punct_subset_ball hb
      have hc := cubWeil_carry e hρ0 N hN (S x) (S y) (hSd x) (hSd y) (hSp x) (hSp y) 1 (by
        rw [hS0 x, hS0 y]
        have h1 : unitOn (1 : ℂˣ) = 1 := map_one _
        rw [h1]
        exact hTw x y hx) _ hbm
      have hz' := (hopen _ hb).2.2.2 N 1 hN _ (hSp x _ hbm) _ (hSp y _ hbm) hc
      exact exists_int_of_exp_eq_one hN hz'
  obtain ⟨L, hLH, hLr⟩ := key
  refine ⟨ρ, (FU.Di i).La, inferInstance, L, e, hρ0, hρ1, fun w hw => ?_⟩
  have hz1 := expCover_mem_punct L.a_le hw
  have hzρ := hU _ hz1
  have hzb := punct_subset_ball hzρ
  have hmem : ∀ x, L.P w x ∈ e.per ((ρ : ℂ) • expCover a w) := fun x => by
    have h : L.P w x ∈ (L.P w).range := ⟨x, rfl⟩
    rw [hLr w hw] at h
    exact (hQ' _ hzb _).1 h
  refine ⟨fun p => ⟨fun hp => ?_, ?_⟩, fun N ζ x x' hN hc => ?_⟩
  · have h : p ∈ (L.P w).range := by
      rw [hLr w hw]
      exact (hQ' _ hzb _).2 hp
    exact h
  · rintro ⟨x, rfl⟩
    exact hmem x
  · have h1 := (hopen _ hzρ).2.2.2 N ζ hN _ (hmem x) _ (hmem x') hc
    have h2 := L.im w hw x x'
    rw [hLH] at h2
    have h3 : ∀ r : ℝ, r = ((L.E x x' : ℤ) : ℝ) →
        (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (r : ℂ) / N) →
        (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((L.E x x' : ℤ) : ℂ) / N) := fun r hr h => by
      rw [h, hr]
      push_cast
      rfl
    exact h3 _ h2 h1

end GlobalTheory.CompanionTheory.Ar.Flat.Link
end
end
