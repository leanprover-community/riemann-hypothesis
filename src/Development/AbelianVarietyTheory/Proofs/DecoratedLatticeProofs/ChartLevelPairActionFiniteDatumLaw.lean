import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntSubIsLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsKeepStandardLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentHalfEqRationalAddNsmulStandardHom
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIffOfCarries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelElementSameCharacterNearBad
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterEqOneOfDeepAtSplitBadPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSwapR
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharacterEqAtDetRootsOfCongruent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulMemStdHom
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdAtToEAfOfIsIdemSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartBasePairDatumRationalApproxEqTwisted
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainMoveCharactersEqRhoUpToBase
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PolOfFnOfOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalMoveClassRepIffLocalConditions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesPreimageUnderLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfRat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianTwistedRealReadingEntireAndInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnStepsAreStandardHermitianPairsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionMovesByTranslatePair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalCongruenceFixesDefiniteStepVector
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepAverageKillsThetaOfDenseFamily
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLocalPlaceLocalModelsLinearSubspace

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker

noncomputable section
namespace GlobalTheory.LevLaw

theorem heisO_smul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (x : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T x (c • f) = c • heisO ψ S T x f := by
  funext t
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem omega_eq_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ e (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ vac Φ w, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (intVec D _) (intVec D _) vac → IsSBHalf e (stdHom S T) Φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (stdHom S T) 1 vac Φ w → ∀ k ∈ GfC S, ∀ k' ∈ GfC T, (∀ x, x ∈ stdHom S T ↔ actO S T k k' x ∈ stdHom S T) → ∀ p q : ℂ, om (k, k') vac = p • vac → (∀ z, IsHalf e z → p * Φ (actO S T k⁻¹ k'⁻¹ z) = q * Φ z) → om (k, k') w = q • w := by
  intro D ψ θ S T a b hS hT δ sc hstd μ om hW e SS hSS vac Φ w hvac hΦ hw k hk k' hk' hkeep p q hp hq
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hSS
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum hSS
  have sdS0 := GlobalTheory.SplitMove.selfDual_int S hstd.gS
  have sdT0 := GlobalTheory.SplitMove.selfDual_int T hstd.gT
  have hth : IsThetaFunO ψ S T vac := hvac.2.theta
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hw
  have th0 := GlobalTheory.SchrTheta.isTheta_placeModel D ψ hstd.std S T _ _ sdS0 sdT0 e hee hinf vac hth T₀ hT₀
  have pm := GlobalTheory.SplitMove.isPlaceModel_move₂ hW hkeep hT₀ th0
  rw [hp] at pm
  have omm : ∀ r s (X : WO S T → ℂ), om r (om s X) = om (r * s) X := fun r s X => by
    rw [map_mul]; rfl

  have hv0 : vac ≠ 0 := by
    intro h0
    obtain ⟨⟨m, hm⟩, hn⟩ := hvac.2.norm
    have h1 := hn m hm
    rw [h0] at h1
    simp [nrm2] at h1
  have hp0 : p ≠ 0 := by
    intro h0
    apply hv0
    have e1 : om (k⁻¹, k'⁻¹) (om (k, k') vac) = vac := by
      rw [omm, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one]; rfl
    rw [hp, h0, zero_smul, map_zero] at e1
    exact e1.symm
  set L := om (k, k') ∘ₗ T₀ ∘ₗ LinearMap.funLeft ℂ ℂ (actO S T k k') with hL
  have pm2 : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (stdHom S T) 1 vac (p⁻¹ • L) := by
    refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩
    · rw [LinearMap.smul_apply, LinearMap.smul_apply, pm.trans Ψ hΨ x hx, heisO_smul]
    · rw [LinearMap.smul_apply, LinearMap.smul_apply, pm.modul Ψ hΨ y hy, heisO_smul]
    · rw [LinearMap.smul_apply, pm.vac, smul_smul, inv_mul_cancel₀ hp0, one_smul]
  have w1 : w = T₀ Φ := hall T₀ hT₀
  have w2 : w = (p⁻¹ • L) Φ := hall _ pm2

  have hfun : q • (fun t => Φ (actO S T k k' t)) = p • Φ := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases hz : IsHalf e (actO S T k k' z)
    · have h1 := hq _ hz
      rw [GlobalTheory.SplitHecke.actO_inv_actO] at h1
      exact h1.symm
    · have h2 : Φ (actO S T k k' z) = 0 := by
        by_contra hne; exact hz (hΦ.1 _ hne)
      have h3 : Φ z = 0 := by
        by_contra hne; exact hz (GlobalTheory.SplitHecke.isHalf_actO k k' (hΦ.1 _ hne))
      rw [h2, h3, mul_zero, mul_zero]
  have eL : L Φ = om (k, k') (T₀ fun t => Φ (actO S T k k' t)) := rfl
  calc om (k, k') w = om (k, k') (T₀ Φ) := by rw [← w1]
    _ = p⁻¹ • om (k, k') (T₀ (p • Φ)) := by
        rw [map_smul, map_smul, smul_smul, inv_mul_cancel₀ hp0, one_smul]
    _ = p⁻¹ • om (k, k') (T₀ (q • fun t => Φ (actO S T k k' t))) := by rw [hfun]
    _ = q • (p⁻¹ • L) Φ := by
        rw [map_smul, map_smul, LinearMap.smul_apply, eL, smul_comm]
    _ = q • w := by rw [← w2]

end GlobalTheory.LevLaw
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilAction_eq_smul_of_keeps_lattice : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ e (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ vac Φ w, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (intVec D _) (intVec D _) vac → IsSBHalf e (stdHom S T) Φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (stdHom S T) 1 vac Φ w → ∀ k ∈ GfC S, ∀ k' ∈ GfC T, (∀ x, x ∈ stdHom S T ↔ actO S T k k' x ∈ stdHom S T) → ∀ p q : ℂ, om (k, k') vac = p • vac → (∀ z, IsHalf e z → p * Φ (actO S T k⁻¹ k'⁻¹ z) = q * Φ z) → om (k, k') w = q • w := by
  atlas_forward_decl GlobalTheory.LevLaw.omega_eq_smul
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartLevels_keep_standardLattice : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i ≤ B.R.m) β, ∀ k ∈ A.U i β, Moves _ (rankN (I.rec7 l Z) i hi) k (Formalism.L2.Col.stdLat B.fields.E _) := by
  first | exact @GlobalTheory.AdForm.levels_keep_stdLat | exact GlobalTheory.AdForm.levels_keep_stdLat | (intros; apply GlobalTheory.AdForm.levels_keep_stdLat <;> assumption)
end

section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.SBMove

open Formalism.L2.Col in

theorem isFrame_one_std {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (n : ℕ) : Formalism.L2.DIV.IsFrame (F := F) 1 (Formalism.L2.Col.stdLat E n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro x
    simp only [inv_one, Units.val_one, Matrix.one_mulVec, IsEmpty.forall_iff, iff_true]
    rw [Subsingleton.elim x 0]; exact zero_mem _
  · haveI : NeZero n := ⟨hn.ne'⟩
    have e : Formalism.L2.Col.stdLat E n = baseLb E n ∅ := by
      ext x
      rw [rll_mem_baseLb]
      constructor
      · intro h
        have h' : ∀ j, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = x j := fun j =>
          (Submodule.mem_one).1 ((Submodule.mem_pi).1 h j (Set.mem_univ _))
        choose r hr using h'
        exact ⟨r, hr, fun P hP => absurd hP (Finset.notMem_empty _)⟩
      · rintro ⟨r, hr, -⟩
        exact (Submodule.mem_pi).2 fun j _ => (Submodule.mem_one).2 ⟨r j, hr j⟩
    intro x
    rw [e, rll_mem_hat_base, inv_one, Units.val_one, Matrix.one_mulVec]
    constructor
    · rintro ⟨y, hy, -⟩ i
      exact hy i ▸ (y i).2
    · exact fun h => ⟨fun i => ⟨x i, h i⟩, fun _ => rfl, fun P hP => absurd hP (Finset.notMem_empty _)⟩

theorem mulVec_mem_sub {A : Type} [CommRing A] {n : ℕ} (R : Subring A) (M : Matrix (Fin n) (Fin n) A)
    (hM : ∀ a b, M a b ∈ R) (v : Fin n → A) (hv : ∀ i, v i ∈ R) (i : Fin n) : (M *ᵥ v) i ∈ R := by
  simp only [Matrix.mulVec, dotProduct]
  exact R.sum_mem fun j _ => R.mul_mem (hM i j) (hv j)

theorem isFrame_of_int {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {L : Submodule (𝓞 E) (Fin n → E)} (hL : Formalism.L2.DIV.IsFrame (F := F) 1 L)
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (h1 : ∀ a b, (β : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) a b ∈ Formalism.L2.Herm.intAf F E)
    (h2 : ∀ a b, ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) a b ∈
      Formalism.L2.Herm.intAf F E) : Formalism.L2.DIV.IsFrame β L := by
  intro x
  rw [hL x, inv_one, Units.val_one, Matrix.one_mulVec]
  constructor
  · intro hx i; exact mulVec_mem_sub _ _ h2 x hx i
  · intro hx i
    have e : x = (β : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ
        (((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e]; exact mulVec_mem_sub _ _ h1 _ hx i

theorem int_of_moves {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V)
    (h : Moves V hn g (Formalism.L2.Col.stdLat D.host.E n)) (a b : Fin V.rank) :
    toEAf D (Formalism.L2.Theta.mt V g⁻¹ a b) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have hmem : (Pi.single (Fin.cast hn b) 1 : Fin n → D.host.E) ∈ Formalism.L2.Col.stdLat D.host.E n := by
    refine (Submodule.mem_pi).2 fun j _ => ?_
    by_cases hj : j = Fin.cast hn b
    · subst hj; simp only [Pi.single_eq_same]; exact Submodule.one_le.1 le_rfl
    · rw [Pi.single_eq_of_ne hj]; exact zero_mem _
  have h' := (h _).1 hmem (Fin.cast hn a)
  have e : (fun j => eToEAf D ((Pi.single (Fin.cast hn b) 1 : Fin n → D.host.E) j)) =
      Pi.single (Fin.cast hn b) 1 := by
    funext j
    by_cases hj : j = Fin.cast hn b
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj]
  rw [e, Matrix.mulVec_single_one] at h'
  simpa [finM, Matrix.reindex_apply] using h'

end GlobalTheory.SBMove

namespace GlobalTheory.SBMove

theorem mt_mul_inv_eq {D : D7} (V : HSp D) (g : GA D V) :
    Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
  simp only [Formalism.L2.Theta.mt]
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem actO_actO_inv {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h (actO S T g⁻¹ h⁻¹ x) = x := by
  simp only [actO, inv_inv]
  simp only [← Matrix.mul_assoc]
  rw [mt_mul_inv_eq, Matrix.one_mul, Matrix.mul_assoc, mt_mul_inv_eq, Matrix.mul_one]

theorem actO_add' {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  simp only [actO, Matrix.mul_add, Matrix.add_mul]

theorem actO_zero' {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) :
    actO S T g h 0 = 0 := by
  simp only [actO, Matrix.mul_zero, Matrix.zero_mul]

theorem actO_nsmul {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (y : WO S T) (k : ℕ) :
    actO S T g h (k • y) = k • actO S T g h y := by
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul, actO_zero']
  | succ k ih => rw [succ_nsmul, succ_nsmul, actO_add', ih]

theorem actO_add_nsmul {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (x y : WO S T) (k : ℕ) :
    actO S T g h (x + k • y) = actO S T g h x + k • actO S T g h y := by
  rw [actO_add', actO_nsmul]

theorem actO_isHalf {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (e : AE D) {x : WO S T} (hx : IsHalf e x) :
    IsHalf e (actO S T g h x) := by
  have hx' : x = e • x := by
    ext a b; exact (hx a b).symm
  have key : actO S T g h x = e • actO S T g h x := by
    conv_lhs => rw [hx']
    simp only [actO, Matrix.mul_smul, Matrix.smul_mul]
  intro i j
  have := congrFun (congrFun key i) j
  rw [Matrix.smul_apply, smul_eq_mul] at this
  exact this.symm

theorem coe_stdLat {D : D7} (n : ℕ) :
    ((Formalism.L2.Col.stdLat D.host.E n : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = intVec D n := by
  ext x
  simp only [SetLike.mem_coe, intVec, Set.mem_setOf_eq]
  rw [Formalism.L2.Col.stdLat, Submodule.mem_pi]
  refine forall_congr' fun k => ?_
  simp only [Set.mem_univ, true_implies, Submodule.mem_one]
  constructor
  · rintro ⟨y, hy⟩; rw [← hy]; exact y.isIntegral_coe
  · intro hk; exact ⟨⟨x k, hk⟩, rfl⟩

theorem actO_mem_stdHom {D : D7} (S T : HSp D) {n m : ℕ} (hn : S.rank = n) (hm : T.rank = m) (g : GA D S) (h : GA D T)
    (hg : Moves S hn g (Formalism.L2.Col.stdLat D.host.E n)) (hg' : Moves S hn g⁻¹ (Formalism.L2.Col.stdLat D.host.E n))
    (hh : Moves T hm h (Formalism.L2.Col.stdLat D.host.E m)) (hh' : Moves T hm h⁻¹ (Formalism.L2.Col.stdLat D.host.E m))
    {x : WO S T} (hx : x ∈ stdHom S T) : actO S T g h x ∈ stdHom S T := by
  have e : stdHom S T = latO S T ((Formalism.L2.Col.stdLat D.host.E S.rank : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) : Set (Fin S.rank → D.host.E))
      ((Formalism.L2.Col.stdLat D.host.E T.rank : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) : Set (Fin T.rank → D.host.E)) fun _ => True := by
    rw [coe_stdLat, coe_stdLat]
  rw [e] at hx ⊢
  have fr : ∀ (V : HSp D) {k : ℕ} (hk : V.rank = k) (b : GA D V), Moves V hk b (Formalism.L2.Col.stdLat D.host.E k) →
      Moves V hk b⁻¹ (Formalism.L2.Col.stdLat D.host.E k) →
      Formalism.L2.DIV.IsFrame (Matrix.GeneralLinearGroup.map (toEAf D) (matHom V b)) (Formalism.L2.Col.stdLat D.host.E V.rank) := by
    intro V k hk b hb hb'
    refine isFrame_of_int (isFrame_one_std _) _ (fun a c => ?_) (fun a c => ?_)
    · have := int_of_moves V hk b⁻¹ hb' a c
      rw [inv_inv] at this
      exact this
    · rw [← map_inv, ← map_inv]
      exact int_of_moves V hk b hb a c
  exact GlobalTheory.AdelicLatMove.actO_mem_latO S T g h _ _ _ _ 1 (Matrix.GeneralLinearGroup.map (toEAf D) (matHom S g)) 1
    (Matrix.GeneralLinearGroup.map (toEAf D) (matHom T h)) (isFrame_one_std _) (fr S hn g hg hg') (isFrame_one_std _)
    (fr T hm h hh hh') (by rw [Units.val_one, Matrix.mul_one]; rfl) (by rw [Units.val_one, Matrix.mul_one]; rfl) x hx

end GlobalTheory.SBMove

open GlobalTheory.SBMove in

theorem GlobalTheory.SBMove.isSBHalf_actO_lev : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ, ∀ Φ : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ, IsSBHalf A.e (stdHom _ _) Φ → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ), IsSBHalf A.e (stdHom _ _) (fun z => Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ z)) := by
  intro B X I hI hP l Z u a Ch A hA i hi α γ Φ hΦ κ κ'
  have hi0 : i ≤ B.R.m := Nat.le_of_succ_le hi
  have hU : ∀ j (hj : j ≤ B.R.m) (β : Ch j) g, g ∈ A.U j β →
      Moves _ (rankN (I.rec7 l Z) j hj) g (Formalism.L2.Col.stdLat B.fields.E _) :=
    fun j hj β g hg => GlobalTheory.AdForm.levels_keep_stdLat I hI hP l Z u a Ch A hA j hj β g hg
  have hG : ∀ x ∈ stdHom _ _, actO _ _ κ.1⁻¹ κ'.1⁻¹ x ∈ stdHom _ _ := fun x hx =>
    actO_mem_stdHom _ _ _ _ _ _ (hU i hi0 α _ (inv_mem κ.2)) (hU i hi0 α _ (by rw [inv_inv]; exact κ.2))
      (hU (i + 1) hi γ _ (inv_mem κ'.2)) (hU (i + 1) hi γ _ (by rw [inv_inv]; exact κ'.2)) hx
  have hH : ∀ x ∈ stdHom _ _, actO _ _ κ.1 κ'.1 x ∈ stdHom _ _ := fun x hx =>
    actO_mem_stdHom _ _ _ _ _ _ (hU i hi0 α _ κ.2) (hU i hi0 α _ (inv_mem κ.2))
      (hU (i + 1) hi γ _ κ'.2) (hU (i + 1) hi γ _ (inv_mem κ'.2)) hx
  obtain ⟨hsupp, k, hk, hinv, hden⟩ := hΦ
  refine ⟨fun t ht => ?_, k, hk, fun v hv hve t => ?_, fun t ht => ?_⟩
  · rw [← actO_actO_inv κ.1 κ'.1 t]
    exact actO_isHalf _ _ _ (hsupp _ ht)
  · show Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ (t + k • v)) = Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ t)
    rw [actO_add_nsmul]
    exact hinv _ (hG v hv) (actO_isHalf _ _ _ hve) _
  · have h1 := hden _ ht
    rw [← actO_nsmul] at h1
    rw [← actO_actO_inv κ.1 κ'.1 (k • t)]
    exact hH _ h1
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhatHalf_adelicHomPairAction_levels : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ, ∀ Φ : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ, IsSBHalf A.e (stdHom _ _) Φ → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ), IsSBHalf A.e (stdHom _ _) (fun z => Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ z)) := by
  atlas_forward_decl GlobalTheory.SBMove.isSBHalf_actO_lev
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

open Formalism.L2.DIV Formalism.L2.Col Formalism.UG GlobalTheory.Mem.Col2.AdT GlobalTheory.Mem.Col2.TC

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.LevelAll

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

theorem adAt_one_apply (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (r s : Fin n) :
    adAt F P ((1 : Matrix (Fin n) (Fin n) (AfE F E)) r s) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s := by
  rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp

theorem conj_bound (hc : CMData F E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1) {u : GL (Fin n) (AfE F E)}
    (hu : u ∈ UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)) (P : HeightOneSpectrum (𝓞 E)) (ε : WithZero (Multiplicative ℤ)) (hε : ε < 1)
    (hP : ∀ r s, Valued.v (adAt F P (u.1 r s) - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ ε) (r s : Fin n) :
    Valued.v (adAt F (conjPrime₂ P) (u.1 r s) - (1 : Matrix (Fin n) (Fin n) ((conjPrime₂ P).adicCompletion E)) r s) ≤ ε := by
  subst hJ
  have hinv := GlobalTheory.Mem.Col2.AdT.Opn.inv_eq_cT hc.sig hu
  have h1 : (1 + ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1)) *
      (1 + cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1)) = 1 := by
    rw [← hinv, add_sub_cancel, Units.mul_inv]
  have h2 := congrArg (adAt F (conjPrime₂ P)).mapMatrix h1
  rw [map_mul, map_add, map_add, map_one] at h2
  have key := GlobalTheory.Mem.Col2.AdT.Opn.val_inv_le Valued.v _ _ h2 ε hε (fun a b => ?_) r s
  · have e : ((adAt F (conjPrime₂ P)).mapMatrix ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1)) r s =
        adAt F (conjPrime₂ P) (u.1 r s) - (1 : Matrix (Fin n) (Fin n) ((conjPrime₂ P).adicCompletion E)) r s := by
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, map_sub, adAt_one_apply]
    rw [← e]; exact key
  · show Valued.v (adAt F (conjPrime₂ P) (sigR hc.sig (FiniteAdeleRing (𝓞 F) F) (((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1) b a))) ≤ ε
    rw [GlobalTheory.Mem.Col2.valued_sigR hc, GlobalTheory.CharValCompare.conjP_conjP, Matrix.sub_apply, map_sub, adAt_one_apply]
    exact hP b a

end Gen

theorem map_prod_cases {G M κ : Type} [Monoid G] [Monoid M] (f : κ → G) (c : G →* M)
    (hpair : ∀ P P' : κ, P ≠ P' → c (f P) = 1 ∨ c (f P') = 1) :
    ∀ L : List κ, L.Nodup → c (L.map f).prod = 1 ∨ ∃ P ∈ L, c (L.map f).prod = c (f P) := by
  have hall : ∀ (P : κ) (L : List κ), c (f P) ≠ 1 → (∀ P' ∈ L, P' ≠ P) → c (L.map f).prod = 1 := by
    intro P L h1 hL
    induction L with
    | nil => simp
    | cons P' L ih =>
      rw [List.map_cons, List.prod_cons, map_mul, ih fun x hx => hL x (List.mem_cons_of_mem _ hx), mul_one]
      exact (hpair P P' (Ne.symm (hL P' (List.mem_cons.2 (Or.inl rfl))))).resolve_left h1
  intro L
  induction L with
  | nil => intro _; left; simp
  | cons P L ih =>
    intro hL
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons, map_mul]
    by_cases h1 : c (f P) = 1
    · rw [h1, one_mul]
      rcases ih hL.2 with h | ⟨P', hP', h⟩
      · exact Or.inl h
      · exact Or.inr ⟨P', List.mem_cons_of_mem _ hP', h⟩
    · rw [hall P L h1 fun P' hP' e => hL.1 (e ▸ hP'), mul_one]
      exact Or.inr ⟨P, List.mem_cons.2 (Or.inl rfl), rfl⟩

set_option maxHeartbeats 12000000 in

theorem exists_level_elt_all : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad), GlobalTheory.Mem.Col2.AdT.ChiFin I l Z S → ∀ (N : ℕ) (g : TC.GA B (B.R.N i)), ∃ z : S.U, S.chi z = 1 ∧ (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E, ∀ r s, adAt B.host.F P (((g * (show TC.GA B (B.R.N i) from z.1) : TC.GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧ ∀ (P : HeightOneSpectrum (𝓞 B.host.E)) (r s : Fin (B.R.N i)), Valued.v (adAt B.host.F P (((show TC.GA B (B.R.N i) from z.1) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s - (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s)) ≤ WithZero.exp (-(N : ℤ)) := by
  intro B X I hOk hPins l Z a T i hi bad S hChi N g
  classical
  have : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  have hgr : gramN (I.rec7 l Z) i hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z).2.2.2 i hi).1
  let cP : ∀ P : HeightOneSpectrum (𝓞 B.fields.E), GA B (B.R.N i) →* Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (P.adicCompletion B.fields.E) :=
    fun P => (RingHom.mapMatrix (adAt B.host.F P)).toMonoidHom.comp (Units.coeHom _)
  have cP_apply : ∀ P (g : GA B (B.R.N i)) r s, cP P g r s = adAt B.host.F P ((g : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) := fun _ _ _ _ => rfl
  let ι : S.U →* GA B (B.R.N i) := S.U.subtype
  have hexp : WithZero.exp (-((max N 1 : ℕ) : ℤ)) ≤ WithZero.exp (-(N : ℤ)) := WithZero.exp_le_exp.2 (by omega)
  have hexp1 : WithZero.exp (-((max N 1 : ℕ) : ℤ)) < 1 := by
    rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by omega)
  have hs : ∀ P : SBof I a, GlobalTheory.TwU.seamP (sm I l Z) P.1 = P.1 := fun P => (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a (B.R.N i) 0 P 1).1
  have hsep : ∀ P P' : SBof I a, P ≠ P' → P.1 ∈ I.Q a → (P'.1 = P.1 ∨ P'.1 = Formalism.L2.Col.conjPrime₂ P.1) → False := by
    intro P P' hne hP h
    rcases h with h | h
    · exact hne (Subtype.ext h.symm)
    obtain ⟨v, hv, hv'⟩ := LevelElt.place_under I hOk hPins l Z a P hP
    apply hv' P' (Ne.symm hne)
    rw [hs] at hv ⊢
    have hc := congrArg HeightOneSpectrum.asIdeal ((GlobalTheory.Mem.Col2.under_eq_iff B.host P.1 P'.1).2 (Or.inr h))
    exact Eq.trans hv hc.symm
  have hsel : ∀ P : SBof I a, ∃ z : S.U, S.chi z = 1 ∧
      (∀ Q : HeightOneSpectrum (𝓞 B.fields.E), cP Q (ι z) = 1 ∨ (P.1 ∈ I.Q a ∧ (Q = P.1 ∨ Q = Formalism.L2.Col.conjPrime₂ P.1))) ∧
      (∀ (Q : HeightOneSpectrum (𝓞 B.fields.E)) r s, Valued.v (cP Q (ι z) r s - (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Q.adicCompletion B.fields.E)) r s) ≤ WithZero.exp (-(N : ℤ))) ∧
      (P.1 ∈ I.Q a → ∃ γ : GL (Fin (B.R.N i)) B.fields.E, ∀ r s, adAt B.host.F P.1 (((g * (show GA B (B.R.N i) from z.1) : GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = algebraMap B.fields.E (P.1.adicCompletion B.fields.E) ((γ : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E) r s)) := by
    intro P
    by_cases hP : P.1 ∈ I.Q a
    · obtain ⟨v, hv, -⟩ := LevelElt.place_under I hOk hPins l Z a P hP
      obtain ⟨z, hz1, hz2, hz3, hz4⟩ := LevelElt.one_prime I hOk hPins l Z a T i hi bad S hChi P hP v hv (max N 1) g 1
      have hzU := ((S.U_eq _).1 z.2).1
      have hbP := ((GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a (B.R.N i) (max N 1) P z.1).2.2).1 hz3
      have hvP := hv
      rw [hs] at hvP
      have hoff : ∀ Q : HeightOneSpectrum (𝓞 B.fields.E), ¬ (Q = P.1 ∨ Q = Formalism.L2.Col.conjPrime₂ P.1) → cP Q (ι z) = 1 := fun Q hQ =>
        Matrix.ext fun r s => by
          rw [cP_apply]
          exact LevelElt.support_one z.1 v hz2 Q (fun hO => hQ ((GlobalTheory.Mem.Col2.under_eq_iff B.host P.1 Q).1
            (HeightOneSpectrum.ext (Eq.trans (Eq.symm hO) hvP)))) r s
      refine ⟨z, hz1, fun Q => ?_, fun Q r s => ?_, fun _ => ?_⟩
      · by_cases hQ : Q = P.1 ∨ Q = Formalism.L2.Col.conjPrime₂ P.1
        · exact Or.inr ⟨hP, hQ⟩
        · exact Or.inl (hoff Q hQ)
      · by_cases hQ : Q = P.1 ∨ Q = Formalism.L2.Col.conjPrime₂ P.1
        · rw [cP_apply]
          rcases hQ with rfl | rfl
          · exact (hbP r s).trans hexp
          · exact (conj_bound (I.rec7 l Z).sp.cm hgr hzU P.1 _ hexp1 hbP r s).trans hexp
        · rw [hoff Q hQ, sub_self, Valuation.map_zero]
          exact zero_le'
      · obtain ⟨γ, hγ⟩ := hz4
        exact ⟨γ, fun r s => by rw [← hγ r s, mul_one]⟩
    · refine ⟨1, map_one _, fun Q => Or.inl (by rw [map_one, map_one]), fun Q r s => ?_, fun h => absurd h hP⟩
      rw [map_one, map_one, sub_self, Valuation.map_zero]; exact zero_le'
  choose zf hzf1 hzf2 hzf3 hzf4 using hsel
  have hpair : ∀ (Q : HeightOneSpectrum (𝓞 B.fields.E)) (P P' : SBof I a), P ≠ P' → cP Q (ι (zf P)) = 1 ∨ cP Q (ι (zf P')) = 1 := by
    intro Q P P' hne
    rcases hzf2 P Q with h | ⟨hP, hQ⟩
    · exact Or.inl h
    rcases hzf2 P' Q with h' | ⟨-, hQ'⟩
    · exact Or.inr h'
    exfalso
    apply hsep P P' hne hP
    rcases hQ with rfl | rfl <;> rcases hQ' with h2 | h2
    · exact Or.inl h2.symm
    · refine Or.inr ?_
      rw [h2, GlobalTheory.CharValCompare.conjP_conjP]
    · exact Or.inr h2.symm
    · have h3 := congrArg Formalism.L2.Col.conjPrime₂ h2
      rw [GlobalTheory.CharValCompare.conjP_conjP, GlobalTheory.CharValCompare.conjP_conjP] at h3
      exact Or.inl h3.symm
  have hone : ∀ P P' : SBof I a, P' ≠ P → cP P'.1 (ι (zf P)) = 1 := by
    intro P P' hne
    rcases hzf2 P P'.1 with h | ⟨hP, hQ⟩
    · exact h
    · exact (hsep P P' hne.symm hP hQ).elim
  have hlistP : ∀ (L : List (SBof I a)), L.Nodup → ∀ P' : SBof I a, cP P'.1 (ι (L.map zf).prod) = if P' ∈ L then cP P'.1 (ι (zf P')) else 1 := by
    intro L
    induction L with
    | nil => intro _ P'; simp
    | cons P L ih =>
      intro hL P'
      rw [List.nodup_cons] at hL
      rw [List.map_cons, List.prod_cons, map_mul, map_mul, ih hL.2]
      by_cases h : P = P'
      · subst h
        simp [hL.1]
      · rw [hone P P' (Ne.symm h)]
        simp [Ne.symm h]
  obtain ⟨w, hw⟩ : ∃ w : S.U, w = ((Finset.univ : Finset (SBof I a)).toList.map zf).prod := ⟨_, rfl⟩
  have hwP : ∀ P : SBof I a, cP P.1 (ι w) = cP P.1 (ι (zf P)) := fun P => by
    rw [hw, hlistP _ (Finset.nodup_toList _) P, if_pos (Finset.mem_toList.2 (Finset.mem_univ _))]
  have hchiw : S.chi w = 1 := by
    rw [hw, map_list_prod]
    refine List.prod_eq_one fun x hx => ?_
    rw [List.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [List.mem_map] at hz
    obtain ⟨P, -, rfl⟩ := hz
    exact hzf1 P
  have hQsub : ∀ P ∈ I.Q a, P ∈ SBof I a := fun P hP => by
    show P ∈ uSG _ _
    exact Finset.mem_union_right _ hP
  refine ⟨w, hchiw, fun P hP => ?_, fun Q r s => ?_⟩
  · obtain ⟨γ, hγ⟩ := hzf4 ⟨P, hQsub P hP⟩ hP
    refine ⟨(γ : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E), fun r s => ?_⟩
    have e0 : cP P (ι w) = cP P (ι (zf ⟨P, hQsub P hP⟩)) := hwP ⟨P, hQsub P hP⟩
    have e1 : cP P (g * ι w) = cP P (g * ι (zf ⟨P, hQsub P hP⟩)) := by rw [map_mul, map_mul, e0]
    have e2 := congrFun (congrFun e1 r) s
    exact (cP_apply P _ r s).symm.trans (e2.trans ((cP_apply P _ r s).trans (hγ r s)))
  · rw [map_sub, adAt_one_apply]
    change Valued.v (cP Q (ι w) r s - (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Q.adicCompletion B.fields.E)) r s) ≤ _
    rcases map_prod_cases zf ((cP Q).comp ι) (hpair Q) _ (Finset.nodup_toList _) with h | ⟨P, -, h⟩
    · rw [← hw] at h
      change cP Q (ι w) = _ at h
      rw [h, sub_self, Valuation.map_zero]; exact zero_le'
    · rw [← hw] at h
      change cP Q (ι w) = _ at h
      rw [h]; exact hzf3 P Q r s

end GlobalTheory.Mem.Col2.AdT.LevelAll

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trivialCharLevel_elt_rational_at_twistPrimes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad), GlobalTheory.Mem.Col2.AdT.ChiFin I l Z S → ∀ (N : ℕ) (g : TC.GA B (B.R.N i)), ∃ z : S.U, S.chi z = 1 ∧ (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E, ∀ r s, adAt B.host.F P (((g * (show TC.GA B (B.R.N i) from z.1) : TC.GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧ ∀ (P : HeightOneSpectrum (𝓞 B.host.E)) (r s : Fin (B.R.N i)), Valued.v (adAt B.host.F P (((show TC.GA B (B.R.N i) from z.1) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s - (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s)) ≤ WithZero.exp (-(N : ℤ)) := by
  atlas_forward_decl GlobalTheory.Mem.Col2.AdT.LevelAll.exists_level_elt_all
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.AdForm.LevLift

theorem exists_mem_U_finM : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i ≤ B.R.m) (β : Ch i) (z : (A.K i hi β).lev.U), ∃ w : A.U i β, z.1.1 = finM _ (rankN (I.rec7 l Z) i hi) w.1 := by
  intro B X I _ _ l Z u a Ch A hA i hi β z
  letI := tensTopL (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E)
    (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)
  obtain ⟨e, he⟩ := GlobalTheory.FinPartIso.exists_finIso (I.rec7 l Z) ((I.rec7 l Z).sp.X i) _ (rankN (I.rec7 l Z) i hi)
  obtain ⟨g, hg⟩ := e.toMulEquiv.surjective ⟨z.1, (((A.K i hi β).lev.U_eq z.1).1 z.2).1⟩
  have hfin : z.1.1 = finM _ (rankN (I.rec7 l Z) i hi) g.1 := by
    rw [← he g]
    have h2 : (e g : GL _ _) = z.1 := congrArg Subtype.val hg
    rw [h2]
  exact ⟨⟨g.1, (hA.U i hi β g.1).2 ⟨g.2, z, hfin⟩⟩, hfin⟩

end GlobalTheory.AdForm.LevLift
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartLevel_exists_adelicLevel_trivialReal_lift : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i ≤ B.R.m) (β : Ch i) (z : (A.K i hi β).lev.U), ∃ w : A.U i β, z.1.1 = finM _ (rankN (I.rec7 l Z) i hi) w.1 := by
  atlas_forward_decl GlobalTheory.AdForm.LevLift.exists_mem_U_finM
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharacter_eq_at_det_roots_of_congruent : ∀ (D : D7) (c : (AE D)ˣ →* Circle), IsHeckeChar D c → ∃ N₀ : ℕ, ∀ (V : HSp D) {n : ℕ} (hn : V.rank = n) (g w : GA D V), w ∈ GfC V → (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (r s : Fin n), Valued.v (adAt D.host.F P (finM V hn w r s - (1 : Matrix (Fin n) (Fin n) (EF D)) r s)) ≤ WithZero.exp (-(N₀ : ℤ))) → ∀ x, IsDetRoot V g x → ∃ x₁, IsDetRoot V (g * w) x₁ ∧ c x₁ = c x := by
  first | exact @GlobalTheory.DetRootApprox.exists_root_same_value | exact GlobalTheory.DetRootApprox.exists_root_same_value | (intros; apply GlobalTheory.DetRootApprox.exists_root_same_value <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.AdForm.DeepMove

section Val
variable {R Γ : Type} [CommRing R] [LinearOrderedCommGroupWithZero Γ] (v : Valuation R Γ)

theorem one_entry_le {n : ℕ} (r s : Fin n) : v ((1 : Matrix (Fin n) (Fin n) R) r s) ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem inv_entry_le {n : ℕ} (X Y : Matrix (Fin n) (Fin n) R) (hXY : X * Y = 1) {ε : Γ} (hε : ε < 1)
    (hX : ∀ r s, v ((X - 1) r s) ≤ ε) : ∀ r s, v ((Y - 1) r s) ≤ ε := by
  have hY : Y - 1 = -((X - 1) * Y) := by
    rw [Matrix.sub_mul, hXY, Matrix.one_mul, neg_sub]
  have hb : ∀ r s, v (Y r s) ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨r, s, hrs⟩ := hcon
    obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ (fun p : Fin n × Fin n => v (Y p.1 p.2))
      ⟨(r, s), Finset.mem_univ _⟩
    have hm : 1 < v (Y p.1 p.2) := lt_of_lt_of_le hrs (hp (r, s) (Finset.mem_univ _))
    have h2 : v ((Y - 1) p.1 p.2) < v (Y p.1 p.2) := by
      rw [hY, Matrix.neg_apply, Valuation.map_neg, Matrix.mul_apply]
      refine lt_of_le_of_lt (Valuation.map_sum_le _ (g := ε * v (Y p.1 p.2)) fun k _ => ?_) ?_
      · rw [map_mul]
        exact mul_le_mul' (hX _ _) (hp (k, p.2) (Finset.mem_univ _))
      · exact mul_lt_of_lt_one_left (zero_lt_one.trans hm) hε
    have e : Y p.1 p.2 = (1 : Matrix (Fin n) (Fin n) R) p.1 p.2 + (Y - 1) p.1 p.2 := by
      rw [Matrix.sub_apply]; ring
    have h3 : v (Y p.1 p.2) < v (Y p.1 p.2) := by
      calc v (Y p.1 p.2) = v ((1 : Matrix (Fin n) (Fin n) R) p.1 p.2 + (Y - 1) p.1 p.2) := by rw [← e]
        _ ≤ max (v ((1 : Matrix (Fin n) (Fin n) R) p.1 p.2)) (v ((Y - 1) p.1 p.2)) := Valuation.map_add _ _ _
        _ < v (Y p.1 p.2) := max_lt ((one_entry_le v _ _).trans_lt hm) h2
    exact lt_irrefl _ h3
  intro r s
  rw [hY, Matrix.neg_apply, Valuation.map_neg, Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul]
  calc _ ≤ ε * 1 := mul_le_mul' (hX _ _) (hb _ _)
    _ = ε := mul_one _

theorem moved_entry_le {a b : ℕ} (X : Matrix (Fin a) (Fin a) R) (Y : Matrix (Fin b) (Fin b) R) (M : Matrix (Fin b) (Fin a) R)
    {ε : Γ} (hε : ε ≤ 1) (hX : ∀ r s, v ((X - 1) r s) ≤ ε) (hY : ∀ r s, v ((Y - 1) r s) ≤ ε)
    (hM : ∀ r s, v (M r s) ≤ 1) : ∀ r s, v ((Y * M * X - M) r s) ≤ ε := by
  have hXb : ∀ r s, v (X r s) ≤ 1 := fun r s => by
    have e : X r s = (1 : Matrix (Fin a) (Fin a) R) r s + (X - 1) r s := by rw [Matrix.sub_apply]; ring
    rw [e]
    exact (Valuation.map_add _ _ _).trans (max_le (one_entry_le v _ _) ((hX r s).trans hε))
  have e : Y * M * X - M = (Y - 1) * M * X + M * (X - 1) := by
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one]; abel
  have h1 : ∀ r s, v (((Y - 1) * M : Matrix (Fin b) (Fin a) R) r s) ≤ ε := fun r s => by
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun k _ => ?_
    rw [map_mul]
    calc _ ≤ ε * 1 := mul_le_mul' (hY _ _) (hM _ _)
      _ = ε := mul_one _
  intro r s
  rw [e, Matrix.add_apply]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
  · rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun k _ => ?_
    rw [map_mul]
    calc _ ≤ ε * 1 := mul_le_mul' (h1 _ _) (hXb _ _)
      _ = ε := mul_one _
  · rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun k _ => ?_
    rw [map_mul]
    calc _ ≤ 1 * ε := mul_le_mul' (hM _ _) (hX _ _)
      _ = ε := one_mul _

end Val

theorem exists_exp_le_natCast {E : Type} [Field E] [NumberField E] (L : ℕ) (hL : 0 < L) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ P : HeightOneSpectrum (𝓞 E),
      WithZero.exp (-(N₀ : ℤ)) ≤ Valued.v ((L : ℕ) : P.adicCompletion E) := by
  set m := Ideal.absNorm (Ideal.span {((L : ℕ) : 𝓞 E)}) with hm
  have hL0 : ((L : ℕ) : 𝓞 E) ≠ 0 := by exact_mod_cast hL.ne'
  have hm0 : m ≠ 0 := by
    rw [hm, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hL0
  refine ⟨m, Nat.one_le_iff_ne_zero.2 hm0, fun P => ?_⟩
  have e1 : ((L : ℕ) : P.adicCompletion E) = algebraMap E _ (algebraMap (𝓞 E) E ((L : ℕ) : 𝓞 E)) := by simp
  rw [e1, GlobalTheory.Mem.Col2.valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
  by_contra h
  push_neg at h
  have hd := (HeightOneSpectrum.intValuation_le_pow_iff_dvd P _ m).1 h.le
  have h2 : Ideal.absNorm (P.asIdeal ^ m) ∣ m := map_dvd Ideal.absNorm hd
  rw [map_pow] at h2
  have hP1 : Ideal.absNorm P.asIdeal ≠ 1 := fun h1 => P.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h1)
  have hP0 : Ideal.absNorm P.asIdeal ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hP2 : 2 ≤ Ideal.absNorm P.asIdeal := by omega
  have h3 : 2 ^ m ≤ m := (Nat.pow_le_pow_left hP2 m).trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) h2)
  exact absurd h3 (not_le.2 (Nat.lt_two_pow_self))

end GlobalTheory.AdForm.DeepMove

namespace GlobalTheory.AdForm.DeepMove

theorem map_sub_one_apply {R R' : Type} [CommRing R] [CommRing R'] {n : ℕ} (f : R →+* R') (A : Matrix (Fin n) (Fin n) R)
    (r s : Fin n) : f ((A - 1) r s) = (A.map f - 1) r s := by
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.map_apply, map_sub]
  split_ifs <;> simp

theorem exists_den_mat {D : D7} {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) : ∃ d : ℕ, 0 < d ∧
    ∀ r s, toEAf D ((d : AE D) * M r s) ∈ Formalism.L2.DIV.RInt D.host.F D.host.E := by
  choose x y hy e using fun r s => GlobalTheory.AdeleBaseChange.exists_approx (F := D.host.F) (E := D.host.E) (toEAf D (M r s))
  obtain ⟨d, hd, hint⟩ := GlobalTheory.AdeleBaseChange.exists_nat_mul_integral
    (Finset.image (fun p : Fin m × Fin n => x p.1 p.2) Finset.univ)
  refine ⟨d, hd, fun r s => ?_⟩
  obtain ⟨z, hz⟩ := hint (x r s) (Finset.mem_image.2 ⟨(r, s), Finset.mem_univ _, rfl⟩)
  rw [map_mul, map_natCast, e r s, mul_add]
  refine add_mem ?_ (mul_mem (natCast_mem _ d) (hy r s))
  have hc : ((d : ℕ) : Formalism.L2.DIV.AfE D.host.F D.host.E) =
      ((d : ℕ) : D.host.E) ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    (map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := D.host.F) (A := D.host.E)
      (B := FiniteAdeleRing (𝓞 D.host.F) D.host.F)) d).symm
  have e2 : ((d : ℕ) : Formalism.L2.DIV.AfE D.host.F D.host.E) * (x r s ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F)) =
      (algebraMap (𝓞 D.host.E) D.host.E z) ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
    rw [hc, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hz, nsmul_eq_mul]
  rw [e2]
  exact GlobalTheory.AdForm.CongAtIdem.tmul_one_mem_rInt z.isIntegral_coe

theorem actO_deep : ∀ (D : D7) (S T : HSp D) {a b : ℕ} (ha : S.rank = a) (hb : T.rank = b) (e : AE D) (M : WO S T), IsHalf e M → ∀ (k : ℕ), 0 < k → ∃ N₀ : ℕ, ∀ (w : GA D S) (w' : GA D T), w ∈ GfC S → w' ∈ GfC T → (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (r s : Fin a), Valued.v (adAt D.host.F P (finM S ha w r s - (1 : Matrix (Fin a) (Fin a) (EF D)) r s)) ≤ WithZero.exp (-(N₀ : ℤ))) → (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (r s : Fin b), Valued.v (adAt D.host.F P (finM T hb w' r s - (1 : Matrix (Fin b) (Fin b) (EF D)) r s)) ≤ WithZero.exp (-(N₀ : ℤ))) → ∃ t : WO S T, t ∈ stdHom S T ∧ IsHalf e t ∧ actO S T w⁻¹ w'⁻¹ M = M + k • t := by
  intro D S T a b ha hb e M hM k hk
  subst ha
  subst hb
  obtain ⟨K, hK, hKm⟩ := GlobalTheory.AdForm.exists_nsmul_mem_stdHom S T
  obtain ⟨d, hd, hdM⟩ := exists_den_mat (D := D) M
  obtain ⟨N₀, hN₀, hN⟩ := exists_exp_le_natCast (E := D.host.E) (d * (k * K)) (Nat.mul_pos hd (Nat.mul_pos hk hK))
  refine ⟨N₀, fun w w' hw hw' hA hB => ?_⟩
  have hc0 : (((k * K : ℕ) : D.host.E)) ≠ 0 := Nat.cast_ne_zero.2 (Nat.mul_pos hk hK).ne'
  have hact : actO S T w⁻¹ w'⁻¹ M = ((Formalism.L2.Theta.mt T w'⁻¹ * (M : Matrix (Fin T.rank) (Fin S.rank) (AE D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) * Formalism.L2.Theta.mt S w⁻¹⁻¹ : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := rfl
  rw [inv_inv] at hact
  obtain ⟨Dm, hDm⟩ : ∃ Dm : WO S T, Dm = actO S T w⁻¹ w'⁻¹ M - M := ⟨_, rfl⟩
  let t₀ : WO S T := Matrix.of fun i j => incA D (((k * K : ℕ) : D.host.E))⁻¹ * Dm i j
  have hent : ∀ i j, Dm i j = (((k * K : ℕ) : AE D)) * t₀ i j := fun i j => by
    have h1 : (((k * K : ℕ) : AE D)) = incA D (((k * K : ℕ) : D.host.E)) := (map_natCast (incA D) _).symm
    have h2 : incA D (((k * K : ℕ) : D.host.E)) * incA D (((k * K : ℕ) : D.host.E))⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hc0, map_one]
    show Dm i j = (((k * K : ℕ) : AE D)) * (incA D (((k * K : ℕ) : D.host.E))⁻¹ * Dm i j)
    rw [h1, ← mul_assoc, h2, one_mul]
  have hkt : k • (K • t₀) = Dm := by
    ext i j
    rw [hent i j]
    simp only [Matrix.smul_apply, nsmul_eq_mul]
    push_cast
    ring
  refine ⟨K • t₀, hKm t₀ ?_ ?_, ?_, ?_⟩
  ·
    have hY : (Formalism.L2.Theta.mt S w).map (infPart D) = 1 :=
      (GlobalTheory.FinPl.KOpen.map_eq_one_iff _ _).2 ((GlobalTheory.FinPl.KOpen.mem_GfC_iff S w).1 hw)
    have hX : (Formalism.L2.Theta.mt T w'⁻¹).map (infPart D) = 1 :=
      (GlobalTheory.FinPl.KOpen.map_eq_one_iff _ _).2 ((GlobalTheory.FinPl.KOpen.mem_GfC_iff T w'⁻¹).1 (inv_mem hw'))
    have h0 : Dm.map (infPart D) = 0 := by
      have e3 : (((Formalism.L2.Theta.mt T w'⁻¹ * (M : Matrix (Fin T.rank) (Fin S.rank) (AE D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) * Formalism.L2.Theta.mt S w : Matrix (Fin T.rank) (Fin S.rank) (AE D))).map (infPart D) = M.map (infPart D) := by
        rw [Matrix.map_mul, Matrix.map_mul, hX, hY, Matrix.one_mul, Matrix.mul_one]
      rw [hDm, hact]
      ext i j
      have e5 := congrFun (congrFun e3 i) j
      simp only [Matrix.map_apply] at e5
      simp only [Matrix.map_apply, Matrix.sub_apply, map_sub, e5, sub_self, Matrix.zero_apply]
    ext i j
    have := congrFun (congrFun h0 i) j
    simp only [Matrix.map_apply, Matrix.zero_apply] at this ⊢
    simp only [t₀, Matrix.of_apply, map_mul, this, mul_zero]
  ·
    intro i j
    refine (mem_rInt_iff _ _ _).2 fun P => ?_
    show Valued.v (adAt D.host.F P (toEAf D (t₀ i j))) ≤ 1
    let φ : AE D →+* P.adicCompletion D.host.E := (adAt D.host.F P).comp (toEAf D)
    have hε : WithZero.exp (-(N₀ : ℤ)) < 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    have hXw : ∀ r s, Valued.v (((Formalism.L2.Theta.mt S w).map φ - 1) r s) ≤ WithZero.exp (-(N₀ : ℤ)) := fun r s => by
      have h := hA P r s
      rw [GlobalTheory.AdForm.CongAtIdem.finM_rfl] at h
      rw [← map_sub_one_apply]
      simpa [φ, Matrix.sub_apply, Matrix.one_apply, Matrix.map_apply, apply_ite] using h
    have hXw' : ∀ r s, Valued.v (((Formalism.L2.Theta.mt T w').map φ - 1) r s) ≤ WithZero.exp (-(N₀ : ℤ)) := fun r s => by
      have h := hB P r s
      rw [GlobalTheory.AdForm.CongAtIdem.finM_rfl] at h
      rw [← map_sub_one_apply]
      simpa [φ, Matrix.sub_apply, Matrix.one_apply, Matrix.map_apply, apply_ite] using h
    have hinv : (Formalism.L2.Theta.mt T w').map φ * (Formalism.L2.Theta.mt T w'⁻¹).map φ = 1 := by
      rw [← Matrix.map_mul, ← GlobalTheory.AdForm.CongAtIdem.mt_mul', mul_inv_cancel, GlobalTheory.AdForm.CongAtIdem.mt_one',
        Matrix.map_one _ (map_zero _) (map_one _)]
    have hY' := inv_entry_le Valued.v _ _ hinv hε hXw'
    let Md : Matrix (Fin T.rank) (Fin S.rank) (AE D) := Matrix.of fun r s => (d : AE D) * M r s
    have hMd : ∀ r s, Valued.v (Md.map φ r s) ≤ 1 := fun r s => by
      have := (mem_rInt_iff _ _ _).1 (hdM r s) P
      exact this
    have hmv := moved_entry_le Valued.v _ _ _ hε.le hXw hY' hMd i j
    have hDmd : (d : AE D) * Dm i j = (((Formalism.L2.Theta.mt T w'⁻¹ * Md : Matrix (Fin T.rank) (Fin S.rank) (AE D)) * Formalism.L2.Theta.mt S w : Matrix (Fin T.rank) (Fin S.rank) (AE D)) - Md) i j := by
      have hs : Md = (d : AE D) • (M : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by ext r s; simp [Md]
      rw [hDm, hact, hs, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub]
      simp [Matrix.smul_apply]
    have hφ : φ ((d : AE D) * Dm i j) = ((Formalism.L2.Theta.mt T w'⁻¹).map φ * Md.map φ * (Formalism.L2.Theta.mt S w).map φ - Md.map φ) i j := by
      have e4 : (((Formalism.L2.Theta.mt T w'⁻¹ * Md : Matrix (Fin T.rank) (Fin S.rank) (AE D)) * Formalism.L2.Theta.mt S w : Matrix (Fin T.rank) (Fin S.rank) (AE D))).map φ =
          (Formalism.L2.Theta.mt T w'⁻¹).map φ * Md.map φ * (Formalism.L2.Theta.mt S w).map φ := by
        rw [Matrix.map_mul, Matrix.map_mul]
      rw [hDmd, ← e4, Matrix.sub_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply, map_sub]
    rw [← hφ, hent i j, ← mul_assoc, ← Nat.cast_mul, map_mul, map_natCast, map_mul] at hmv
    have hL := hN P
    have hL0 : Valued.v (((d * (k * K) : ℕ)) : P.adicCompletion D.host.E) ≠ 0 := fun h0 => by
      rw [h0] at hL
      exact WithZero.exp_ne_zero (le_antisymm hL zero_le')
    have h2 : Valued.v (((d * (k * K) : ℕ)) : P.adicCompletion D.host.E) * Valued.v (φ (t₀ i j)) ≤
        Valued.v (((d * (k * K) : ℕ)) : P.adicCompletion D.host.E) * 1 := by
      rw [mul_one]; exact hmv.trans hL
    calc Valued.v (φ (t₀ i j))
        = (Valued.v (((d * (k * K) : ℕ)) : P.adicCompletion D.host.E))⁻¹ *
          (Valued.v (((d * (k * K) : ℕ)) : P.adicCompletion D.host.E) * Valued.v (φ (t₀ i j))) := (inv_mul_cancel_left₀ hL0 _).symm
      _ ≤ (Valued.v (((d * (k * K) : ℕ)) : P.adicCompletion D.host.E))⁻¹ *
          (Valued.v (((d * (k * K) : ℕ)) : P.adicCompletion D.host.E) * 1) := mul_le_mul' le_rfl h2
      _ = 1 := inv_mul_cancel_left₀ hL0 _
  ·
    have hMe : e • (M : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = M := by ext r s; exact hM r s
    have hDe : ∀ i j, e * Dm i j = Dm i j := fun i j => by
      have h3 : e • (((Formalism.L2.Theta.mt T w'⁻¹ * (M : Matrix (Fin T.rank) (Fin S.rank) (AE D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) * Formalism.L2.Theta.mt S w : Matrix (Fin T.rank) (Fin S.rank) (AE D))) = (((Formalism.L2.Theta.mt T w'⁻¹ * (M : Matrix (Fin T.rank) (Fin S.rank) (AE D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) * Formalism.L2.Theta.mt S w : Matrix (Fin T.rank) (Fin S.rank) (AE D))) := by
        rw [← Matrix.smul_mul, ← Matrix.mul_smul]
        congr 2
      have h4 := congrFun (congrFun h3 i) j
      rw [Matrix.smul_apply, smul_eq_mul] at h4
      rw [hDm, hact, Matrix.sub_apply, mul_sub, h4, hM i j]
    intro i j
    simp only [t₀, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul]
    calc e * ((K : AE D) * (incA D (((k * K : ℕ) : D.host.E))⁻¹ * Dm i j))
        = (K : AE D) * (incA D (((k * K : ℕ) : D.host.E))⁻¹ * (e * Dm i j)) := by ring
      _ = _ := by rw [hDe i j]
  · rw [hkt, hDm]
    abel

end GlobalTheory.AdForm.DeepMove
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfMatrix_move_deepCongruence_bound : ∀ (D : D7) (S T : HSp D) {a b : ℕ} (ha : S.rank = a) (hb : T.rank = b) (e : AE D) (M : WO S T), IsHalf e M → ∀ (k : ℕ), 0 < k → ∃ N₀ : ℕ, ∀ (w : GA D S) (w' : GA D T), w ∈ GfC S → w' ∈ GfC T → (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (r s : Fin a), Valued.v (adAt D.host.F P (finM S ha w r s - (1 : Matrix (Fin a) (Fin a) (EF D)) r s)) ≤ WithZero.exp (-(N₀ : ℤ))) → (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (r s : Fin b), Valued.v (adAt D.host.F P (finM T hb w' r s - (1 : Matrix (Fin b) (Fin b) (EF D)) r s)) ≤ WithZero.exp (-(N₀ : ℤ))) → ∃ t : WO S T, t ∈ stdHom S T ∧ IsHalf e t ∧ actO S T w⁻¹ w'⁻¹ M = M + k • t := by
  atlas_forward_decl GlobalTheory.AdForm.DeepMove.actO_deep
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.RatApprox

theorem mt_mul' {D : D7} (V : HSp D) (g h : GA D V) :
    Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

theorem actO_actO' {D : D7} (S T : HSp D) (g g' : GA D S) (h h' : GA D T) (x : WO S T) :
    actO S T g h (actO S T g' h' x) = actO S T (g * g') (h * h') x := by
  unfold actO
  rw [_root_.mul_inv_rev, mt_mul', mt_mul']
  simp only [Matrix.mul_assoc]

theorem isHalf_actO' {D : D7} {S T : HSp D} {e : AE D} (g : GA D S) (h : GA D T) {u : WO S T} (hu : IsHalf e u) :
    IsHalf e (actO S T g h u) := by
  intro i j
  simp only [actO, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← hu l k]
  ring

end GlobalTheory.AdForm.RatApprox

namespace GlobalTheory.AdForm.RatApprox

set_option maxHeartbeats 2000000 in

theorem approx : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (k : ℕ), 0 < k → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ (z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E), ∃ (κ₁ : A.U i α) (κ₁' : A.U (i + 1) γ) (x₁ y₁ : (AE (I.rec7 l Z))ˣ) (t : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) κ₁.1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧ (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) (i + 1) hi) κ₁'.1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧ IsDetRoot _ κ₁.1 x₁ ∧ IsDetRoot _ κ₁'.1 y₁ ∧ A.chr (i + 1) x₁ = A.chr (i + 1) x ∧ A.chr (i + 1) y₁ = A.chr (i + 1) y ∧ A.chi i α κ₁ = A.chi i α κ ∧ A.chi (i + 1) γ κ₁' = A.chi (i + 1) γ κ' ∧ t ∈ stdHom _ _ ∧ IsHalf A.e t ∧ actO _ _ κ₁.1⁻¹ κ₁'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) = actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) + k • t := by
  intro B X I hI hP l Z u a Ch A hA i hi α γ k hk κ κ' x y hx hy z
  have hi' : i ≤ B.R.m := Nat.le_of_succ_le hi
  obtain ⟨NB, hNB⟩ := GlobalTheory.T.heckeCharacter_eq_at_det_roots_of_congruent (I.rec7 l Z) (A.chr (i + 1)) (hA.chr ⟨i, hi⟩).1
  have hee : A.e * A.e = A.e := GlobalTheory.PlaceDatum.idemSum_mul_self hA.idem
  have hez : IsHalf A.e (z.map fun r => A.e * incA (I.rec7 l Z) r) := fun r s => by
    simp only [Matrix.map_apply, ← mul_assoc, hee]
  have hM := isHalf_actO' κ.1⁻¹ κ'.1⁻¹ hez
  obtain ⟨NC, hNC⟩ := GlobalTheory.T.halfMatrix_move_deepCongruence_bound (I.rec7 l Z) _ _ (rankN (I.rec7 l Z) i hi') (rankN (I.rec7 l Z) (i + 1) hi) A.e _ hM k hk
  have hfin : ∀ j (hj : j ≤ B.R.m) (β : Ch j), GlobalTheory.Mem.Col2.AdT.ChiFin I l Z (A.K j hj β).lev := fun j hj β => by
    obtain ⟨n, hn, h⟩ := hA.fin j hj β
    exact ⟨n, hn, fun κ _ => h κ⟩
  have step : ∀ j (hj : j ≤ B.R.m) (β : Ch j) (g : A.U j β), ∃ w : A.U j β, A.chi j β w = 1 ∧
      (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) j hj) (g * w).1 : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧
      ∀ (P : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E)) (r s : Fin (B.R.N j)), Valued.v (adAt (I.rec7 l Z).host.F P (finM _ (rankN (I.rec7 l Z) j hj) w.1 r s - (1 : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) (EF (I.rec7 l Z))) r s)) ≤ WithZero.exp (-((max NB NC : ℕ) : ℤ)) := by
    intro j hj β g
    obtain ⟨g₀, hg₀⟩ := ((hA.U j hj β g.1).1 g.2).2
    obtain ⟨zz, hz1, hz2, hz3⟩ := GlobalTheory.T.exists_trivialCharLevel_elt_rational_at_twistPrimes I hI hP l Z a _ j hj _ (A.K j hj β).lev (hfin j hj β) (max NB NC) (show TC.GA B (B.R.N j) from g₀.1)
    obtain ⟨w, hw⟩ := GlobalTheory.T.chartLevel_exists_adelicLevel_trivialReal_lift I hI hP l Z u a Ch A hA j hj β zz
    refine ⟨w, ?_, fun P hPQ => ?_, fun P r s => ?_⟩
    · rw [hA.chi j hj β w zz hw, hz1]
    · obtain ⟨M, hM⟩ := hz2 P hPQ
      refine ⟨M, fun r s => ?_⟩
      rw [← hM r s, Subgroup.coe_mul, GlobalTheory.RepLattice.finM_mul', ← hg₀, ← hw]
      rfl
    · rw [← hw]
      exact hz3 P r s
  obtain ⟨w, hw1, hw2, hw3⟩ := step i hi' α κ
  obtain ⟨w', hw1', hw2', hw3'⟩ := step (i + 1) hi γ κ'
  have hwG : w.1 ∈ GfC _ := ((hA.U i hi' α w.1).1 w.2).1
  have hwG' : w'.1 ∈ GfC _ := ((hA.U (i + 1) hi γ w'.1).1 w'.2).1
  have dB : ∀ {n : ℕ} (f : Matrix (Fin n) (Fin n) (EF (I.rec7 l Z))), (∀ (P : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E)) (r s : Fin n), Valued.v (adAt (I.rec7 l Z).host.F P (f r s - (1 : Matrix (Fin n) (Fin n) (EF (I.rec7 l Z))) r s)) ≤ WithZero.exp (-((max NB NC : ℕ) : ℤ))) → ∀ N₀ : ℕ, N₀ ≤ max NB NC → ∀ (P : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E)) (r s : Fin n), Valued.v (adAt (I.rec7 l Z).host.F P (f r s - (1 : Matrix (Fin n) (Fin n) (EF (I.rec7 l Z))) r s)) ≤ WithZero.exp (-(N₀ : ℤ)) := by
    intro n f hf N₀ hN P r s
    exact (hf P r s).trans (WithZero.exp_le_exp.2 (neg_le_neg (Nat.cast_le.2 hN)))
  obtain ⟨x₁, hx₁, hcx⟩ := hNB _ (rankN (I.rec7 l Z) i hi') κ.1 w.1 hwG (dB _ hw3 NB (le_max_left _ _)) x hx
  obtain ⟨y₁, hy₁, hcy⟩ := hNB _ (rankN (I.rec7 l Z) (i + 1) hi) κ'.1 w'.1 hwG' (dB _ hw3' NB (le_max_left _ _)) y hy
  obtain ⟨t, ht, hth, hte⟩ := hNC w.1 w'.1 hwG hwG' (dB _ hw3 NC (le_max_right _ _)) (dB _ hw3' NC (le_max_right _ _))
  refine ⟨κ * w, κ' * w', x₁, y₁, t, hw2, hw2', hx₁, hy₁, hcx, hcy, ?_, ?_, ht, hth, ?_⟩
  · rw [map_mul, hw1, mul_one]
  · rw [map_mul, hw1', mul_one]
  · rw [← hte, actO_actO']
    simp only [Subgroup.coe_mul, _root_.mul_inv_rev]

end GlobalTheory.AdForm.RatApprox
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twistRational_levelElements_same_characters : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (k : ℕ), 0 < k → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ (z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E), ∃ (κ₁ : A.U i α) (κ₁' : A.U (i + 1) γ) (x₁ y₁ : (AE (I.rec7 l Z))ˣ) (t : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) κ₁.1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧ (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) (i + 1) hi) κ₁'.1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧ IsDetRoot _ κ₁.1 x₁ ∧ IsDetRoot _ κ₁'.1 y₁ ∧ A.chr (i + 1) x₁ = A.chr (i + 1) x ∧ A.chr (i + 1) y₁ = A.chr (i + 1) y ∧ A.chi i α κ₁ = A.chi i α κ ∧ A.chi (i + 1) γ κ₁' = A.chi (i + 1) γ κ' ∧ t ∈ stdHom _ _ ∧ IsHalf A.e t ∧ actO _ _ κ₁.1⁻¹ κ₁'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) = actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) + k • t := by
  atlas_forward_decl GlobalTheory.AdForm.RatApprox.approx
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.AdForm.MovedLaw

section Rat
open Formalism.L2.DIV Formalism.L2.Col
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def ratAt (F : Type) [Field F] [NumberField F] [Algebra F E] (n : ℕ) (P : HeightOneSpectrum (𝓞 E)) : Subgroup (GL (Fin n) (AfE F E)) :=
  (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap E (P.adicCompletion E))).range.comap
    (Matrix.GeneralLinearGroup.map (n := Fin n) (adAt F P))

theorem mem_ratAt_of {P : HeightOneSpectrum (𝓞 E)} {g : GL (Fin n) (AfE F E)} (M : Matrix (Fin n) (Fin n) E)
    (h : ∀ r s, adAt F P ((g : Matrix (Fin n) (Fin n) (AfE F E)) r s) = algebraMap E _ (M r s)) : g ∈ ratAt F n P := by
  have e : (adAt F P).mapMatrix (g : Matrix (Fin n) (Fin n) (AfE F E)) = (algebraMap E (P.adicCompletion E)).mapMatrix M := by
    exact Matrix.ext h
  have hu : IsUnit ((adAt F P) (g : Matrix (Fin n) (Fin n) (AfE F E)).det) :=
    ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).map _
  rw [RingHom.map_det, e, ← RingHom.map_det] at hu
  have hM : M.det ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hu
    exact hu.ne_zero rfl
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hM, Units.ext e.symm⟩

theorem of_mem_ratAt {P : HeightOneSpectrum (𝓞 E)} {g : GL (Fin n) (AfE F E)} (h : g ∈ ratAt F n P) :
    ∃ γ : GL (Fin n) E, ∀ r s, adAt F P ((g : Matrix (Fin n) (Fin n) (AfE F E)) r s) =
      algebraMap E (P.adicCompletion E) ((γ : Matrix (Fin n) (Fin n) E) r s) := by
  obtain ⟨γ, hγ⟩ := h
  exact ⟨γ, fun r s => (congrArg (fun z : GL (Fin n) (P.adicCompletion E) => z.1 r s) hγ).symm⟩

theorem ratAt_of_pt [StarRing E] {hc : Formalism.BasicNotions.CMData F E} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} {g : GL (Fin n) (AfE F E)}
    {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) {P : HeightOneSpectrum (𝓞 E)} (hP : P ∈ Q) : g ∈ ratAt F n P :=
  mem_ratAt_of (Matrix.of fun i j => p.fr ⟨P, hP⟩ (Pi.single j 1) i) fun r s => h.fr ⟨P, hP⟩ r s

end Rat

section Step
open Formalism.L2.DIV Formalism.L2.Col
attribute [local instance] GlobalTheory.Mem.Col2.starE
variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem fst_eq_one {u : B.Word} {a : I.ι} {j : ℕ} {b : (I.stp u a j).β} {g : (I.stp u a j).G b} (h : (I.stp u a j).gam b g = 1) :
    g.1 = 1 := Subtype.ext ((toGLm B.fields.E (B.R.N j)).injective (h.trans (map_one _).symm))

theorem act_eq {u : B.Word} {a : I.ι} {j : ℕ} {b : (I.stp u a j).β} {g : (I.stp u a j).G b} (h : (I.stp u a j).gam b g = 1)
    (p : (I.stp u a j).D b) : ((I.stp u a j).act b g p).1.1 =
      ((1, g.2.1.1, g.2.2.1) : UF B.fields.E (B.R.N j) × GLG B.fields.E (B.R.N j) (B.primes X).vGs ×
        GLQ B.fields.E (B.R.N j) (I.Q a)) • p.1.1 := by
  show ((g.1, g.2.1.1, g.2.2.1) : UF B.fields.E (B.R.N j) × GLG B.fields.E (B.R.N j) (B.primes X).vGs ×
        GLQ B.fields.E (B.R.N j) (I.Q a)) • p.1.1 = _
  rw [fst_eq_one h]

theorem cosetIn_act_congr (hI : I.Ok) {u : B.Word} {a : I.ι} {j : ℕ} {b : (I.stp u a j).β} {g : (I.stp u a j).G b}
    (h : (I.stp u a j).gam b g = 1) {p p' : (I.stp u a j).D b} (e : cosetIn p = cosetIn p') :
    cosetIn ((I.stp u a j).act b g p) = cosetIn ((I.stp u a j).act b g p') := by
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1
  funext P
  have hex : ∃ t, AdT.LiftsInv I g P t := by
    by_cases hP : P.1 ∈ (B.primes X).vGs
    · obtain ⟨t, ht⟩ := redGL_surjective (n := B.R.N j) P.1 (g.2.1.1 ⟨P.1, hP⟩)⁻¹
      refine ⟨t.1, t.2, fun _ x hx => ?_, fun hQ => absurd hQ (Finset.disjoint_left.1 hd hP)⟩
      rw [GlobalTheory.TopStep.redV_redGL t hx, ht]
    · have hQ : P.1 ∈ I.Q a := (Finset.mem_union.1 P.2).resolve_left hP
      exact ⟨((g.2.2.1 ⟨P.1, hQ⟩)⁻¹).1, ((g.2.2.1 ⟨P.1, hQ⟩)⁻¹).2, fun h' => absurd h' hP, fun _ => rfl⟩
  obtain ⟨t, ht⟩ := hex
  ext z
  rw [AdT.cosetIn_act_of_liftsInv I hI u a j b g p P t h ht, AdT.cosetIn_act_of_liftsInv I hI u a j b g p' P t h ht, e]

end Step

section Main
open Formalism.L2.DIV Formalism.L2.Col
attribute [local instance] GlobalTheory.Mem.Col2.starE
variable {B : Base} {X : PreX B.toPre} {I : TC B X}

set_option maxHeartbeats 1000000 in

theorem exists_move_of_reads (hI : I.Ok) {u : B.Word} {a : I.ι} {i : ℕ} {Ch : Type} {chOf : (I.stp u a i).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} {U : Ch → Subgroup (TC.GA B (B.R.N i))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u a i).Cl → TC.GA B (B.R.N i)} {st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E}
    {k : Ch → TC.GA B (B.R.N i)} (hR : I.Reads u a i chOf Lb U chi y st k) (c : (I.stp u a i).Cl) (x : U (chOf c))
    (hx : x.1 ∈ UAd B.sp.cm (B.R.N i)) (hr : ∀ P ∈ I.Q a, x.1 ∈ ratAt B.host.F (B.R.N i) P) (p : (I.stp u a i).D c.1)
    (hp : TC.PtOf (k (chOf c)) p.1.1) (hc : cosetIn ((I.stp u a i).rep c) = cosetIn p) :
    ∃ g : (I.stp u a i).G c.1, (I.stp u a i).gam c.1 g = 1 ∧ TC.PtOf (x.1 * k (chOf c)) ((I.stp u a i).act c.1 g p).1.1 ∧
      cosetIn ((I.stp u a i).act c.1 g p) = cosetIn p ∧
      ((chi (chOf c) x : ℂˣ) : ℂ) = B.embLL (((I.stp u a i).chr c.1 g : B.LLˣ) : B.LL) := by
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1
  have hy : TC.PtOf (y c * k (chOf c)) ((I.stp u a i).rep c).1.1 :=
    IsPtOf.of_extTo (ColIn.Q_subset_SQ I a) hd (hR.pt c)
  have e : y c * x.1 * k (chOf c) = y c * k (chOf c) * ((k (chOf c))⁻¹ * x.1 * k (chOf c)) := by group
  have e' : x.1 * k (chOf c) = k (chOf c) * ((k (chOf c))⁻¹ * x.1 * k (chOf c)) := by group
  have hu : y c * x.1 * k (chOf c) ∈ UAd B.sp.cm (B.R.N i) := by
    rw [e]
    exact mul_mem hy.uni (mul_mem (mul_mem (inv_mem hp.uni) hx) hp.uni)
  obtain ⟨q, hq⟩ := GlobalTheory.Mem.Col2.RatFrPt.exists_isPtOf_of_rat B.sp.cm ((B.primes X).vT u) (B.primes X).vGs (I.Q a) _ hu fun P hP => by
    refine of_mem_ratAt ?_
    rw [e]
    exact mul_mem (ratAt_of_pt hy hP) (mul_mem (mul_mem (inv_mem (ratAt_of_pt hp hP)) (hr P hP)) (ratAt_of_pt hp hP))
  obtain ⟨g, h1, h2, h3⟩ := (hR.lev c x.1 q hq).1 x.2
  have hq' : TC.PtOf (y c * x.1 * k (chOf c)) ((I.stp u a i).act c.1 g ((I.stp u a i).rep c)).1.1 := h2 ▸ hq
  refine ⟨g, h1, ?_, ?_, hR.chr c x g h1 hq'⟩
  · rw [e, act_eq h1] at hq'
    obtain ⟨⟨k1, k2, k3, k4⟩, k5⟩ := GlobalTheory.Mem.Col2.TC.ChTw.Match.LocForm.conds_of_pts hy hq'
    rw [e', act_eq h1]
    exact GlobalTheory.Mem.Col2.TC.ChTw.Match.LocForm.pt_of_conds hp k1 k2 k3 k4 k5
  · rw [← cosetIn_act_congr hI h1 hc, h3, hc]

variable {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι} {Ch : ℕ → Type} {A : TwDat I l Z u a Ch}

set_option maxHeartbeats 1000000 in

theorem exists_move (hI : I.Ok) (hA : A.Is) (j : ℕ) (hj : j ≤ B.R.m) (β : Ch j) (κ : A.U j β)
    (hr : ∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) j hj) κ.1 : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s))
    (κ₀ : TC.GA B (B.R.N j)) (h0 : finM _ (rankN (I.rec7 l Z) j hj) κ.1 = κ₀.1) :
    ∃ g : (I.stp u a j).G (A.b0 j β), (I.stp u a j).gam (A.b0 j β) g = 1 ∧
      TC.PtOf (κ₀ * A.kb j β) ((I.stp u a j).act (A.b0 j β) g (A.p0 j β)).1.1 ∧
      cosetIn ((I.stp u a j).act (A.b0 j β) g (A.p0 j β)) = cosetIn (A.p0 j β) ∧
      ((A.chi j β κ : ℂˣ) : ℂ) = B.embLL (((I.stp u a j).chr (A.b0 j β) g : B.LLˣ) : B.LL) := by
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1
  obtain ⟨c, rfl⟩ := hA.chOf_onto j hj β
  obtain ⟨x, hx⟩ := ((hA.U j hj _ κ.1).1 κ.2).2
  obtain rfl : κ₀ = x.1 := Units.ext (h0.symm.trans hx.symm)
  obtain ⟨hb, hc⟩ := hA.rep j hj c
  have hV : ((I.rec7 l Z).sp.X j).gram = 1 := hI.gram_X j
  have hJ : gramN (I.rec7 l Z) j hj = 1 := by
    unfold gramN
    rw [hV]
    simp
  have hu : x.1 ∈ UAd B.sp.cm (B.R.N j) := by
    have h := (((A.K j hj (A.chOf j c)).lev.U_eq x.1).1 x.2).1
    generalize x.1 = z at h ⊢
    rw [hJ] at h
    exact h
  rw [hA.chi j hj _ κ x hx, ← hb]
  exact exists_move_of_reads hI (hA.reads j hj) c x hu
    (fun P hP => by
      obtain ⟨M, hM⟩ := hr P hP
      exact mem_ratAt_of M (by rw [h0] at hM; exact hM))
    (A.p0 j (A.chOf j c)) ((hA.base j hj _).1.of_extTo (ColIn.Q_subset_SQ I a) hd) hc

set_option maxHeartbeats 1000000 in

theorem chr_root_eq (hI : I.Ok) (hA : A.Is) (j : Fin B.R.m) (k : ℕ) (hk : k ≤ B.R.m) (g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X k))
    (hg : g ∈ GfC _) (y : TC.GA B (B.R.N k)) (hy : finM _ (rankN (I.rec7 l Z) k hk) g = y.1) (x : (AE (I.rec7 l Z))ˣ)
    (hx : IsDetRoot _ g x) (p : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u k) (hp : TC.PtOf y p) :
    (A.chr ((j : ℕ) + 1) x : ℂ)⁻¹ =
      B.embLL (muInvDet (X := B.fields) I.sel (rowSG (B.primes X) I.sel (I.tup a)) (mUof (R := B.R) I.Ch (I.tup a) j.1)
        (muAtT (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) j.1) p.deco.1.N (frsF I.sel (I.tup a) p)) := by
  have hlev := GlobalTheory.Mem.LevTwist.levOk_twists B X I hI
  have hQ := ColIn.Q_subset_SQ I a
  have hd : Disjoint (B.primes X).vGs (I.Q a) := Finset.disjoint_of_subset_right hQ hlev.2.1
  obtain ⟨a', ha'⟩ := GlobalTheory.Mem.DetLift.exists_isDetLift B.R B.host (B.R.N k) _ hp.uni
  have htw := (GlobalTheory.Mem.ReadTwist.isTwist_of_reads B.R B.host _ B.embLL I.S (I.tup a) (I.xi a) (hI.xi_reads a)).1
  have key := GlobalTheory.DetRootRead.chr_at_detRoot (I.rec7 l Z) (A.chr ((j : ℕ) + 1)) (I.C.mu0 j * I.xi a) (hA.chr j)
    (Formalism.L2.Host.HChar.TrivOn.mul (I.C.isMu0 j).triv htw.2.1) _ _ _ _ hg hy _ hx a' ha'
  have hfac : KDq B.host (I.Q a) ≤ ((I.C.mu0 j * I.xi a).1.comp (Chr.finPartI B.host.E)).ker := fun b hb => by
    have e : (I.C.mu0 j).1 (Chr.finPartI B.host.E b) = 1 := reference_characters_factor_tame (I.Q a) I.C j hb
    have e' : (I.xi a).1 (Chr.finPartI B.host.E b) = 1 := (hlev.2.2 a).1 hb
    show (I.C.mu0 j).1 (Chr.finPartI B.host.E b) * (I.xi a).1 (Chr.finPartI B.host.E b) = 1
    rw [e, e', one_mul]
  have hp' : IsPtOf (host_cmData B.R B.host) y (extTo (I.Q a) p) := by
    rw [extTo_self hd]
    exact hp
  rw [GlobalTheory.LvT.Built.KMap.map_muInvDet_pt I hI a u j p, key, ← xiDet_eq I.SQ ((KDq_anti B.host hQ).trans hfac), xiDet,
    ← tildeQ_toDtQ hQ hfac, DetProj.toDtQ_detPt B.R B.host _ _ _ _ _ hQ p hlev.1,
    ← GlobalTheory.Mem.Col2.DetSpec.mk_eq_detPt B.R B.host _ _ _ _ _ _ _ a' (hlev.1.mono hQ) hp' ha', tildeQ_mk _ _ hfac]
  rfl

set_option maxHeartbeats 1000000 in

theorem chr_root_eq_prod (hI : I.Ok) (hA : A.Is) (j : Fin B.R.m) (k : ℕ) (hk : k ≤ B.R.m) (β : Ch k) (κ : A.U k β)
    (κ₀ : TC.GA B (B.R.N k)) (h0 : finM _ (rankN (I.rec7 l Z) k hk) κ.1 = κ₀.1) (x : (AE (I.rec7 l Z))ˣ) (hx : IsDetRoot _ κ.1 x)
    (g : (I.stp u a k).G (A.b0 k β)) (hg : (I.stp u a k).gam (A.b0 k β) g = 1)
    (hq : TC.PtOf (κ₀ * A.kb k β) ((I.stp u a k).act (A.b0 k β) g (A.p0 k β)).1.1)
    (t : GLQ B.fields.E (B.R.N k) (rowSG (B.primes X) I.sel (I.tup a)))
    (ht : ∀ P, frsF I.sel (I.tup a) ((I.stp u a k).act (A.b0 k β) g (A.p0 k β)).1.1 P =
      g.1.1 * (frsF I.sel (I.tup a) (A.p0 k β).1.1 P * (t P).1)) :
    (A.chr ((j : ℕ) + 1) x : ℂ)⁻¹ = B.embLL (∏ P : rowSG (B.primes X) I.sel (I.tup a),
      rhoS (R := B.R) I.Ch I.sel (I.tup a) j.1 P ((LinearEquiv.det (t P).1 : B.fields.Eˣ) : B.fields.E)) := by
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1
  obtain ⟨hkA, hkAm, hxr⟩ := hA.kA k hk β
  have hκ := ((hA.U k hk β κ.1).1 κ.2).1
  have hfin : finM _ (rankN (I.rec7 l Z) k hk) (κ.1 * A.kA k β) = (κ₀ * A.kb k β).1 := by
    rw [GlobalTheory.RepLattice.finM_mul', h0, hkAm, Units.val_mul]
    rfl
  have e1 := chr_root_eq hI hA j k hk _ (mul_mem hκ hkA) _ hfin _ (GlobalTheory.TwistFinPart.isDetRoot_mul' _ _ _ _ _ hx hxr) _ hq
  have e2 := chr_root_eq hI hA j k hk _ hkA _ hkAm _ hxr _ ((hA.base k hk β).1.of_extTo (ColIn.Q_subset_SQ I a) hd)
  have hD := muDetLaw_chain (Pr := B.primes X) I.Ch I.sel (I.tup a) (I.cst a) j.1 (B.R.N k)
  rw [muAt_eq_muAtT I.Ch I.sel (I.tup a) (I.cst a) (muqTie_of_ok _ _ _ _ _ (hI.idx_ok a)) j.1 j.2] at hD
  have hN : ((I.stp u a k).act (A.b0 k β) g (A.p0 k β)).1.1.deco.1.N = (A.p0 k β).1.1.deco.1.N := by
    rw [act_eq hg]
    exact Submodule.map_id _
  have hF : frsF I.sel (I.tup a) ((I.stp u a k).act (A.b0 k β) g (A.p0 k β)).1.1 =
      fun P => frsF I.sel (I.tup a) (A.p0 k β).1.1 P * (t P).1 := funext fun P => by
    rw [ht P, fst_eq_one hg]
    exact one_mul _
  rw [hN, hF] at e1
  unfold muInvDet at e1 e2
  simp only [hD _ _ _, Finset.prod_mul_distrib] at e1
  rw [← mul_assoc, map_mul B.embLL, ← e2, map_mul, Circle.coe_mul, mul_inv, mul_comm] at e1
  exact mul_left_cancel₀ (inv_ne_zero (Circle.coe_ne_zero _)) e1

end Main

set_option maxHeartbeats 2000000 in

theorem moved_law : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (κ : A.U i α) (κ' : A.U (i + 1) γ), (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) κ.1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) → (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) (i + 1) hi) κ'.1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) → ∀ x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ (κ₀ : TC.GA B (B.R.N i)) (κ₀' : TC.GA B (B.R.N (i + 1))), finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) κ.1 = κ₀.1 → finM _ (rankN (I.rec7 l Z) (i + 1) hi) κ'.1 = κ₀'.1 → ∃ (q : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1)), TC.PtOf (κ₀ * A.kb i α) q.1.1 ∧ TC.PtOf (κ₀' * A.kb (i + 1) γ) q'.1.1 ∧ cosetIn q = cosetIn (A.p0 i α) ∧ cosetIn q' = cosetIn (A.p0 (i + 1) γ) ∧ ∀ w : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)), (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i (A.b0 i α) (A.b0 (i + 1) γ) q q' w) = ((A.chi i α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (i + 1) γ κ' : ℂˣ) : ℂ) * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i (A.b0 i α) (A.b0 (i + 1) γ) (A.p0 i α) (A.p0 (i + 1) γ) w) := by
  intro B X I hI _ l Z u a Ch A hA i hi α γ κ κ' hr hr' x y hx hy κ₀ κ₀' h0 h0'
  have hi0 := Nat.le_of_succ_le hi
  obtain ⟨g, g1, g2, g3, g4⟩ := exists_move hI hA i hi0 α κ hr κ₀ h0
  obtain ⟨g', g1', g2', g3', g4'⟩ := exists_move hI hA (i + 1) hi γ κ' hr' κ₀' h0'
  refine ⟨_, _, g2, g2', g3, g3', fun w => ?_⟩
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  obtain ⟨t, t', ht, ht', law⟩ := GlobalTheory.KerDia.Eqv.xiAt_law (Pr := B.primes X) hX hPr hI.sel_ok (hI.T_mem u) hI.g_mem (hI.idx_ok a)
    (hI.sharp a) hi (A.b0 i α) (A.b0 (i + 1) γ) g g' (A.p0 i α) (A.p0 (i + 1) γ)
  have e1 := chr_root_eq_prod hI hA ⟨i, hi⟩ i hi0 α κ κ₀ h0 x hx g g1 g2 t ht
  have e2 := chr_root_eq_prod hI hA ⟨i, hi⟩ (i + 1) hi γ κ' κ₀' h0' y hy g' g1' g2' t' ht'
  have key := congrArg B.embLL (law w)
  have hw : (g'.1.1.toLinearMap ∘ₗ w ∘ₗ g.1.1.symm.toLinearMap : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1))) = w := by
    rw [fst_eq_one g1, fst_eq_one g1']
    rfl
  simp only [unitInv_rho I.Ch I.sel (I.tup a) i _ _, Finset.prod_mul_distrib, Finset.prod_inv_distrib] at key
  rw [hw, map_mul, map_mul, map_inv₀, map_mul, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀] at key
  rw [g4, g4', e1, inv_eq_iff_eq_inv.1 e2]
  exact ((mul_comm _ _).trans key).trans (congrArg (· * _) (mul_comm _ _))

end GlobalTheory.AdForm.MovedLaw
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDatum_law_between_basePoints_movedPoints : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (κ : A.U i α) (κ' : A.U (i + 1) γ), (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) κ.1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) → (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) (i + 1) hi) κ'.1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) → ∀ x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ (κ₀ : TC.GA B (B.R.N i)) (κ₀' : TC.GA B (B.R.N (i + 1))), finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) κ.1 = κ₀.1 → finM _ (rankN (I.rec7 l Z) (i + 1) hi) κ'.1 = κ₀'.1 → ∃ (q : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1)), TC.PtOf (κ₀ * A.kb i α) q.1.1 ∧ TC.PtOf (κ₀' * A.kb (i + 1) γ) q'.1.1 ∧ cosetIn q = cosetIn (A.p0 i α) ∧ cosetIn q' = cosetIn (A.p0 (i + 1) γ) ∧ ∀ w : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)), (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i (A.b0 i α) (A.b0 (i + 1) γ) q q' w) = ((A.chi i α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (i + 1) γ κ' : ℂˣ) : ℂ) * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i (A.b0 i α) (A.b0 (i + 1) γ) (A.p0 i α) (A.p0 (i + 1) γ) w) := by
  atlas_forward_decl GlobalTheory.AdForm.MovedLaw.moved_law
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.AdForm.ReadLaw

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem transport_base : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (k : ℕ), 0 < k → (∀ (z₁ z₂ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (t : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), t ∈ stdHom _ _ → IsHalf A.e t → z₁.map (fun r => A.e * incA (I.rec7 l Z) r) = z₂.map (fun r => A.e * incA (I.rec7 l Z) r) + k • t → A.xi i hi α γ z₁ = A.xi i hi α γ z₂) → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) (κ₀ : TC.GA B (B.R.N i)) (κ₀' : TC.GA B (B.R.N (i + 1))), finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) κ.1 = κ₀.1 → finM _ (rankN (I.rec7 l Z) (i + 1) hi) κ'.1 = κ₀'.1 → ∀ (q : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1)), TC.PtOf (κ₀ * A.kb i α) q.1.1 → TC.PtOf (κ₀' * A.kb (i + 1) γ) q'.1.1 → cosetIn q = cosetIn (A.p0 i α) → cosetIn q' = cosetIn (A.p0 (i + 1) γ) → ∀ (z z' : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (v : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), v ∈ stdHom _ _ → IsHalf A.e v → actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) = z'.map (fun r => A.e * incA (I.rec7 l Z) r) + k • v → A.xi i hi α γ z' = B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i (A.b0 i α) (A.b0 (i + 1) γ) q q' (toHom _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) z)) := by
  intro B X I hok hpins l Z u a Ch A hA i hi α γ k hk hper κ κ' κ₀ κ₀' hκ hκ' q q' hq hq' hc hc' z z' v hv hvh hact
  have hi0 := Nat.le_of_succ_le hi
  obtain ⟨d, hd, h1⟩ := GlobalTheory.AdForm.CongAtIdem.cong_at_idem ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))
    (rankN (I.rec7 l Z) i hi0) (rankN (I.rec7 l Z) (i + 1) hi) A.e _ hA.idem
  have hd0 := GlobalTheory.Mem.Df.disjoint_vGs_Q I hok l a
  have hQ := GlobalTheory.Mem.Col2.ColIn.Q_subset_SQ I a
  have hb := hA.base i hi0 α
  have hb' := hA.base (i + 1) hi γ
  obtain ⟨M₀, hM₀, h2⟩ := GlobalTheory.AdForm.TwResid.xiAt_transport_tw I l hok u a i hi (A.b0 i α) (A.b0 (i + 1) γ)
    (A.p0 i α) q (A.p0 (i + 1) γ) q' (A.kb i α) κ₀ (A.kb (i + 1) γ) κ₀'
    (hb.1.of_extTo hQ hd0) hb.2 (hb'.1.of_extTo hQ hd0) hb'.2 hq hq' hc hc'
  obtain ⟨z₂, t, ht, hth, hv2⟩ := GlobalTheory.T.idempotentHalf_eq_rational_add_nsmul_standardHom ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) A.e _ hA.idem
    (d * M₀) (Nat.mul_pos hd hM₀) v hvh
  have hm : (z' + k • z₂).map (fun r => A.e * incA (I.rec7 l Z) r) =
      z'.map (fun r => A.e * incA (I.rec7 l Z) r) + k • z₂.map (fun r => A.e * incA (I.rec7 l Z) r) := by
    have e := map_add (((AddMonoidHom.mulLeft A.e).comp (incA (I.rec7 l Z)).toAddMonoidHom).mapMatrix) z' (k • z₂)
    rw [map_nsmul] at e
    exact e
  have hcong : (z' + k • z₂).map (fun r => A.e * incA (I.rec7 l Z) r) =
      actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) + (d * M₀) • (-(k • t)) := by
    rw [hact, hm, hv2, smul_neg, smul_comm (d * M₀) k t, smul_add]
    abel
  have hc2 := h1 κ.1 κ'.1 κ₀ κ₀' hκ hκ' M₀ z (z' + k • z₂) (-(k • t)) (neg_mem (nsmul_mem ht k)) hcong
  have hx := h2 _ _ hc2
  have hw : IsHalf A.e (v - (d * M₀) • t) := fun r s => by
    rw [Matrix.sub_apply, Matrix.smul_apply, mul_sub, mul_smul_comm, hvh r s, hth r s]
  have hz2 : z₂.map (fun r => A.e * incA (I.rec7 l Z) r) = v - (d * M₀) • t := eq_sub_of_add_eq hv2.symm
  have hp := hper (z' + k • z₂) z' (v - (d * M₀) • t) (sub_mem hv (nsmul_mem ht _)) hw (by rw [hm, hz2])
  exact hp.symm.trans (congrArg B.embLL hx)

theorem law_read : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (k : ℕ), 0 < k → (∀ (z₁ z₂ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (t : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), t ∈ stdHom _ _ → IsHalf A.e t → z₁.map (fun r => A.e * incA (I.rec7 l Z) r) = z₂.map (fun r => A.e * incA (I.rec7 l Z) r) + k • t → A.xi i hi α γ z₁ = A.xi i hi α γ z₂) → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ), (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) κ.1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) → (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) (i + 1) hi) κ'.1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) → ∀ x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ (z z' : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (v : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), v ∈ stdHom _ _ → IsHalf A.e v → actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) = z'.map (fun r => A.e * incA (I.rec7 l Z) r) + k • v → (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * A.xi i hi α γ z' = ((A.chi i α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (i + 1) γ κ' : ℂˣ) : ℂ) * A.xi i hi α γ z := by
  intro B X I hok hpins l Z u a Ch A hA i hi α γ k hk hper κ κ' hr hr' x y hx hy z z' v hv hvh hact
  obtain ⟨κ₀, hκ₀⟩ := ((hA.U i (Nat.le_of_succ_le hi) α κ.1).1 κ.2).2
  obtain ⟨κ₀', hκ₀'⟩ := ((hA.U (i + 1) hi γ κ'.1).1 κ'.2).2
  obtain ⟨q, q', hq, hq', hc, hc', hlaw⟩ := GlobalTheory.T.finiteDatum_law_between_basePoints_movedPoints I hok hpins l Z u a Ch A hA i hi α γ κ κ' hr hr' x y hx hy κ₀.1 κ₀'.1 hκ₀.symm hκ₀'.symm
  have h2 := transport_base I hok hpins l Z u a Ch A hA i hi α γ k hk hper κ κ' κ₀.1 κ₀'.1 hκ₀.symm hκ₀'.symm q q' hq hq' hc hc' z z' v hv hvh hact
  rw [h2]
  exact hlaw _

end GlobalTheory.AdForm.ReadLaw
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDatum_basePoints_law_rational_twistPrimes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (k : ℕ), 0 < k → (∀ (z₁ z₂ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (t : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), t ∈ stdHom _ _ → IsHalf A.e t → z₁.map (fun r => A.e * incA (I.rec7 l Z) r) = z₂.map (fun r => A.e * incA (I.rec7 l Z) r) + k • t → A.xi i hi α γ z₁ = A.xi i hi α γ z₂) → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ), (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) κ.1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) → (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) (i + 1) hi) κ'.1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) → ∀ x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ (z z' : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (v : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), v ∈ stdHom _ _ → IsHalf A.e v → actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) = z'.map (fun r => A.e * incA (I.rec7 l Z) r) + k • v → (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * A.xi i hi α γ z' = ((A.chi i α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (i + 1) γ κ' : ℂˣ) : ℂ) * A.xi i hi α γ z := by
  atlas_forward_decl GlobalTheory.AdForm.ReadLaw.law_read
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.XiLaw

theorem isHalf_add {D : D7} {m n : ℕ} {e : AE D} {u v : Mx D m n} (hu : IsHalf e u) (hv : IsHalf e v) : IsHalf e (u + v) := by
  intro r s
  simp only [Matrix.add_apply, mul_add, hu r s, hv r s]

theorem xi_law : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (k : ℕ), 0 < k → (∀ (z₁ z₂ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (t : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), t ∈ stdHom _ _ → IsHalf A.e t → z₁.map (fun r => A.e * incA (I.rec7 l Z) r) = z₂.map (fun r => A.e * incA (I.rec7 l Z) r) + k • t → A.xi i hi α γ z₁ = A.xi i hi α γ z₂) → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ (z z' : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (v : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), v ∈ stdHom _ _ → IsHalf A.e v → actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) = z'.map (fun r => A.e * incA (I.rec7 l Z) r) + k • v → (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * A.xi i hi α γ z' = ((A.chi i α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (i + 1) γ κ' : ℂˣ) : ℂ) * A.xi i hi α γ z := by
  intro B X I hI hP l Z u a Ch A hA i hi α γ k hk hxi κ κ' x y hx hy z z' v hv hvh hrel
  obtain ⟨κ₁, κ₁', x₁, y₁, t, r1, r1', hx1, hy1, ex, ey, ec, ec', ht, hth, hact⟩ :=
    GlobalTheory.T.exists_twistRational_levelElements_same_characters I hI hP l Z u a Ch A hA i hi α γ k hk κ κ' x y hx hy z
  have key := GlobalTheory.T.finiteDatum_basePoints_law_rational_twistPrimes I hI hP l Z u a Ch A hA i hi α γ k hk hxi κ₁ κ₁' r1 r1' x₁ y₁ hx1 hy1 z z' (v + t)
    (add_mem hv ht) (isHalf_add hvh hth) (by rw [hact, hrel, nsmul_add, add_assoc])
  rw [ex, ey, ec, ec'] at key
  exact key

end GlobalTheory.AdForm.XiLaw
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDatum_law_under_two_levels_mod_half_lattice : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (k : ℕ), 0 < k → (∀ (z₁ z₂ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (t : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), t ∈ stdHom _ _ → IsHalf A.e t → z₁.map (fun r => A.e * incA (I.rec7 l Z) r) = z₂.map (fun r => A.e * incA (I.rec7 l Z) r) + k • t → A.xi i hi α γ z₁ = A.xi i hi α γ z₂) → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ (z z' : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (v : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), v ∈ stdHom _ _ → IsHalf A.e v → actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) = z'.map (fun r => A.e * incA (I.rec7 l Z) r) + k • v → (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * A.xi i hi α γ z' = ((A.chi i α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (i + 1) γ κ' : ℂˣ) : ℂ) * A.xi i hi α γ z := by
  atlas_forward_decl GlobalTheory.AdForm.XiLaw.xi_law
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.RatLaw

theorem isHalf_actO {D : D7} {S T : HSp D} {e : AE D} (g : GA D S) (h : GA D T) {u : WO S T} (hu : IsHalf e u) :
    IsHalf e (actO S T g h u) := by
  intro i j
  simp only [actO, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← hu l k]
  ring

theorem law_rat : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ, ∀ Φ : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ, IsSBHalf A.e (stdHom _ _) Φ → ∀ p : ℂ, (∀ z, Φ (z.map fun r => A.e * incA (I.rec7 l Z) r) = p * A.xi i hi α γ z) → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E, (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r)) = ((A.chi i α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (i + 1) γ κ' : ℂˣ) : ℂ) * Φ (z.map fun r => A.e * incA (I.rec7 l Z) r) := by
  intro B X I hI hP l Z u a Ch A hA i hi α γ Φ hΦ p hp κ κ' x y hx hy z
  obtain ⟨hsupp, k, hk, hper, -⟩ := hΦ
  set ez := z.map fun r => A.e * incA (I.rec7 l Z) r with hez
  by_cases hw : IsHalf A.e (actO _ _ κ.1⁻¹ κ'.1⁻¹ ez)
  · obtain ⟨z', v, hv, hvh, hwe⟩ := GlobalTheory.T.idempotentHalf_eq_rational_add_nsmul_standardHom _ _ A.e _ hA.idem k hk _ hw
    have hΦw : Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ ez) = p * A.xi i hi α γ z' := by
      rw [hwe, hper v hv hvh, hp z']
    rw [hΦw, hp z]
    by_cases hp0 : p = 0
    · simp [hp0]
    · have hxi : ∀ (z₁ z₂ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E)
          (t : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), t ∈ stdHom _ _ → IsHalf A.e t →
          z₁.map (fun r => A.e * incA (I.rec7 l Z) r) = z₂.map (fun r => A.e * incA (I.rec7 l Z) r) + k • t →
          A.xi i hi α γ z₁ = A.xi i hi α γ z₂ := by
        intro z₁ z₂ t ht hth he
        have h1 := hp z₁
        rw [he, hper t ht hth, hp z₂] at h1
        exact (mul_left_cancel₀ hp0 h1).symm
      have hL := GlobalTheory.T.finiteDatum_law_under_two_levels_mod_half_lattice I hI hP l Z u a Ch A hA i hi α γ k hk hxi κ κ' x y hx hy z z' v hv hvh hwe
      linear_combination p * hL
  · have h1 : Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ ez) = 0 := by
      by_contra h
      exact hw (hsupp _ h)
    have h2 : Φ ez = 0 := by
      by_contra h
      exact hw (GlobalTheory.AdForm.RatLaw.isHalf_actO _ _ (hsupp _ h))
    rw [h1, h2]
    simp

end GlobalTheory.AdForm.RatLaw
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDatumLaw_rationalPoints_half : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ, ∀ Φ : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ, IsSBHalf A.e (stdHom _ _) Φ → ∀ p : ℂ, (∀ z, Φ (z.map fun r => A.e * incA (I.rec7 l Z) r) = p * A.xi i hi α γ z) → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E, (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r)) = ((A.chi i α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (i + 1) γ κ' : ℂˣ) : ℂ) * Φ (z.map fun r => A.e * incA (I.rec7 l Z) r) := by
  atlas_forward_decl GlobalTheory.AdForm.RatLaw.law_rat
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.LevDat

set_option synthInstance.maxHeartbeats 200000 in

theorem half_nsmul {D : D7} {m n : ℕ} (e : AE D) (v : Mx D m n) (h : IsHalf e v) (k : ℕ) : IsHalf e (k • v) :=
  fun r c => by
    change e * (k • v r c) = k • v r c
    rw [nsmul_eq_mul, mul_left_comm, h r c, ← nsmul_eq_mul]

theorem sb_step {Y : Type} [AddCommGroup Y] (Λ : AddSubgroup Y) (hf : Y → Prop) (Φ : Y → ℂ) (k : ℕ)
    (hinv : ∀ u ∈ Λ, hf u → ∀ t, Φ (t + k • u) = Φ t) (k' : ℕ) (v : Y) (hv : v ∈ Λ) (hh : hf (k' • v)) (t : Y) :
    Φ (t + (k * k') • v) = Φ t := by
  have h := hinv (k' • v) (AddSubgroup.nsmul_mem Λ hv k') hh t
  rw [← mul_smul] at h
  exact h

set_option maxHeartbeats 1000000 in

theorem levDat_law : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ, ∀ Φ : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ, IsSBHalf A.e (stdHom _ _) Φ → ∀ p : ℂ, (∀ z, Φ (z.map fun r => A.e * incA (I.rec7 l Z) r) = p * A.xi i hi α γ z) → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ z, IsHalf A.e z → (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ z) = ((A.chi i α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (i + 1) γ κ' : ℂˣ) : ℂ) * Φ z := by
  intro B X I hI hP l Z u a Ch A hA i hi α γ Φ hΦ p hp κ κ' x y hx hy z hz
  obtain ⟨hs1, k1, hk1, hinv1, hsup1⟩ := GlobalTheory.T.schwartzBruhatHalf_adelicHomPairAction_levels I hI hP l Z u a Ch A hA i hi α γ Φ hΦ κ κ'
  have hΦ' := hΦ
  obtain ⟨hs2, k2, hk2, hinv2, hsup2⟩ := hΦ'
  obtain ⟨w, v, hv, hvh, hzw⟩ := GlobalTheory.T.idempotentHalf_eq_rational_add_nsmul_standardHom _ _ A.e _ hA.idem (k1 * k2) (Nat.mul_pos hk1 hk2) z hz
  subst hzw
  have e1 := sb_step _ (IsHalf A.e) (fun z => Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ z)) k1 hinv1 k2 v hv
    (half_nsmul _ _ hvh _) (w.map fun r => A.e * incA (I.rec7 l Z) r)
  have e2 := sb_step _ (IsHalf A.e) Φ k2 hinv2 k1 v hv (half_nsmul _ _ hvh _) (w.map fun r => A.e * incA (I.rec7 l Z) r)
  rw [mul_comm k2 k1] at e2
  beta_reduce at e1
  rw [e1, e2]
  exact GlobalTheory.T.finiteDatumLaw_rationalPoints_half I hI hP l Z u a Ch A hA i hi α γ Φ hΦ p hp κ κ' x y hx hy w

end GlobalTheory.LevDat
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_datum_law_under_two_chart_levels : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ, ∀ Φ : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ, IsSBHalf A.e (stdHom _ _) Φ → ∀ p : ℂ, (∀ z, Φ (z.map fun r => A.e * incA (I.rec7 l Z) r) = p * A.xi i hi α γ z) → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ z, IsHalf A.e z → (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ z) = ((A.chi i α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (i + 1) γ κ' : ℂˣ) : ℂ) * Φ z := by
  atlas_forward_decl GlobalTheory.LevDat.levDat_law
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.LevLaw

theorem latFr_stdLat (D : D7) (S : HSp D) (a : ℕ) (hS : S.rank = a) :
    latFr S hS (Formalism.L2.Col.stdLat D.host.E a) = intVec D S.rank := by
  subst hS
  rw [GlobalTheory.LatPairMove.latFr_rfl, coe_colStdLat]

theorem mem_stdHom_iff_actO (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (k : GA D S) (k' : GA D T)
    (h1 : Moves S hS 1 (Formalism.L2.Col.stdLat D.host.E a)) (h1' : Moves T hT 1 (Formalism.L2.Col.stdLat D.host.E b))
    (hk : Moves S hS k (Formalism.L2.Col.stdLat D.host.E a)) (hk' : Moves T hT k' (Formalism.L2.Col.stdLat D.host.E b)) :
    ∀ x, x ∈ stdHom S T ↔ actO S T k k' x ∈ stdHom S T := by
  have key := GlobalTheory.LatPairMove.latO_move D S T a b hS hT 1 k 1 k' _ _ _ _ h1 h1' (by rwa [mul_one]) (by rwa [mul_one])
  rw [latFr_stdLat, latFr_stdLat] at key
  intro x
  constructor
  · intro hx
    exact (key _).2 ⟨x, hx, rfl⟩
  · intro hx
    obtain ⟨u₀, hu₀, he⟩ := (key _).1 hx
    have hinv : ∀ v, actO S T k⁻¹ k'⁻¹ (actO S T k k' v) = v := fun v => by
      have := GlobalTheory.AdelicLatMove.actO_actO_inv S T k⁻¹ k'⁻¹ v
      rwa [inv_inv, inv_inv] at this
    have := congrArg (actO S T k⁻¹ k'⁻¹) he
    rw [hinv, hinv] at this
    rw [this]
    exact hu₀

theorem lev_law : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ Ch : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j) ψ θ x vac c₀ kom dd w Ram rd cK, PinX I l Z ψ θ x vac c₀ → PinColL A ι ψ θ x vac c₀ kom dd w Ram rd cK → ∀ j, j < B.R.m → ∀ α γ (κ : A.U j (ι j α)) (κ' : A.U (j + 1) (ι (j + 1) γ)), kom j (κ.1, κ'.1) (comb ψ _ _ (dd j α γ) (vac j)) = (((A.chi j _ κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (j + 1) _ κ' : ℂˣ) : ℂ)) • comb ψ _ _ (dd j α γ) (vac j) := by
  intro B X I hI hP l Z u a Ch₀ Ch A ι ψ θ x vac c₀ kom dd w Ram rd cK hX hC j hj α γ κ κ'
  have hj1 : j + 1 ≤ B.R.m := hj
  have hstd := GlobalTheory.T.trueColumnSteps_are_standardHermitianPairs I hI hP l Z ψ θ hX.std hX.inf
  have hSP := hstd.1 j hj1
  obtain ⟨xr, hxr⟩ := hstd.2.2.2.2 _ κ.1
  obtain ⟨yr, hyr⟩ := hstd.2.2.2.2 _ κ'.1
  have hU := hC.is.U j (Nat.le_of_succ_le hj1) (ι j α)
  have hU' := hC.is.U (j + 1) hj1 (ι (j + 1) γ)
  have hkG : κ.1 ∈ GfC _ := ((hU κ.1).1 κ.2).1
  have hkG' : κ'.1 ∈ GfC _ := ((hU' κ'.1).1 κ'.2).1
  have h1G : (1 : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) ∈ GfC _ := ((hU 1).1 (one_mem _)).1
  have h1G' : (1 : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X (j + 1))) ∈ GfC _ := ((hU' 1).1 (one_mem _)).1
  have hMk := GlobalTheory.T.chartLevels_keep_standardLattice I hI hP l Z u a Ch₀ A hC.is j (Nat.le_of_succ_le hj1) (ι j α) κ.1 κ.2
  have hMk' := GlobalTheory.T.chartLevels_keep_standardLattice I hI hP l Z u a Ch₀ A hC.is (j + 1) hj1 (ι (j + 1) γ) κ'.1 κ'.2
  have hM1 := GlobalTheory.T.chartLevels_keep_standardLattice I hI hP l Z u a Ch₀ A hC.is j (Nat.le_of_succ_le hj1) (ι j α) 1 (one_mem _)
  have hM1' := GlobalTheory.T.chartLevels_keep_standardLattice I hI hP l Z u a Ch₀ A hC.is (j + 1) hj1 (ι (j + 1) γ) 1 (one_mem _)
  have hom := hC.om j hj
  have hVT := (hX.mv j hj1).2 a (A.chr (j + 1)) (kom j) (hC.is.chr ⟨j, hj⟩) hom
  have e1 := hVT κ.1 hkG κ'.1 hkG' _ _ hMk hMk' xr yr hxr hyr
  have e0 := hVT 1 h1G 1 h1G' _ _ hM1 hM1' 1 1 (GlobalTheory.SmallFix.isDetRoot_one _) (GlobalTheory.SmallFix.isDetRoot_one _)
  have h11 : kom j ((1 : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)), (1 : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X (j + 1)))) = 1 :=
    map_one (kom j)
  set p : ℂ := ((A.chr (j + 1) xr : ℂ))⁻¹ * (A.chr (j + 1) yr : ℂ) with hpdef
  have hvth : IsThetaFunO ψ _ _ (vac j) := (hX.vc j hj).2.theta
  have hp : kom j (κ.1, κ'.1) (vac j) = p • vac j := by
    have hf : IsThetaFunO ψ _ _ (kom j (κ.1, κ'.1) (vac j) - p • vac j) :=
      GlobalTheory.AvgKill.theta_sub' (hom.om_pres _ _ hvth) (GlobalTheory.LocMod.LinSpace.isThetaFunO_smul p hvth)
    have hz : xiN θ _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj1)) (rankN (I.rec7 l Z) (j + 1) hj1) I.A.δ I.A.sc
        (kom j (κ.1, κ'.1) (vac j) - p • vac j) = 0 := by
      funext z
      have a1 := congrFun e1 z
      have a0 := congrFun e0 z
      rw [h11] at a0
      simp only [ColDat.xiS, xiN, Module.End.one_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply, map_one, Circle.coe_one, inv_one, mul_one] at a1 a0 ⊢
      rw [hpdef, mul_sub, show ∀ q r s : ℂ, q * (r * s) = r * (q * s) from fun q r s => by ring]
      erw [a1, a0]
      ring
    exact sub_eq_zero.1 ((GlobalTheory.T.gaussianTwistedRealReading_entire_and_injective _ ψ θ _ _ _ _ _ _ _ _ hSP).2 _ hf hz)
  obtain ⟨-, Φ, hΦ, hΞ, hth⟩ := hC.dat j hj1 α γ
  have hq : ∀ z, IsHalf A.e z → p * Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ z) =
      (((A.chi j _ κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (j + 1) _ κ' : ℂˣ) : ℂ)) * Φ z := fun z hz =>
    GlobalTheory.T.finite_datum_law_under_two_chart_levels I hI hP l Z u a Ch₀ A hC.is j hj1 (ι j α) (ι (j + 1) γ) Φ hΦ (w j α γ) (fun z => hΞ z) κ κ' xr yr hxr hyr z hz
  have hlat := mem_stdHom_iff_actO (I.rec7 l Z) _ _ _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj1))
    (rankN (I.rec7 l Z) (j + 1) hj1) κ.1 κ'.1 hM1 hM1' hMk hMk'
  exact GlobalTheory.T.weilAction_eq_smul_of_keeps_lattice (I.rec7 l Z) ψ θ _ _ _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj1)) (rankN (I.rec7 l Z) (j + 1) hj1)
    I.A.δ I.A.sc hSP (A.chr (j + 1)) (kom j) hom A.e _ hC.is.idem (vac j) Φ _ (hX.vc j hj) hΦ hth κ.1 hkG κ'.1 hkG' hlat p _ hp hq

end GlobalTheory.AdForm.LevLaw
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartLevelPair_action_finiteDatum_law : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ Ch : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j) ψ θ x vac c₀ kom dd w Ram rd cK, PinX I l Z ψ θ x vac c₀ → PinColL A ι ψ θ x vac c₀ kom dd w Ram rd cK → ∀ j, j < B.R.m → ∀ α γ (κ : A.U j (ι j α)) (κ' : A.U (j + 1) (ι (j + 1) γ)), kom j (κ.1, κ'.1) (comb ψ _ _ (dd j α γ) (vac j)) = (((A.chi j _ κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (j + 1) _ κ' : ℂˣ) : ℂ)) • comb ψ _ _ (dd j α γ) (vac j) := by
  atlas_forward_decl GlobalTheory.AdForm.LevLaw.lev_law
end
