import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyBreuilKisinDatumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrobeniusPeriodStatement
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallineLatticePeriodsOnDisc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyDiscPeriodAinfBasisDataOfIsPer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStratifiedPhiModuleCrystallineLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeIffIsBaseChange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrismCoverReceivingBreuilKisin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveAndRangeOfPrismCover
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStratifiedPhiModuleValue
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemilinearProjectiveModuleCompose
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInjectivePushoutOfPrismCover
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinHomEisensteinSpanAndNonZeroDivisor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismCoverInjectiveAndDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeExistsBasisEqImageOfBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalFrobeniusPullbackBasis

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_crystalline_lattice_periods_on_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (P : LocPrime l) (AI : LocAinf l P), IsStd P AI → ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (L : Lattice (O := ℤ_[l]) ρ), (∀ x, Continuous fun g => ρ g x) → IsCrys (P.PD K) ρ → ∀ (d : ℕ) (b : Module.Basis (Fin d) ℤ_[l] ↥L.T), Nonempty (Seed bk d (fun g => LinearMap.toMatrix b b (actT L g)) τ) := by
  first | exact @GlobalTheory.SeedExists.exists_seed | exact GlobalTheory.SeedExists.exists_seed | (intros; apply GlobalTheory.SeedExists.exists_seed <;> assumption)
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_discPeriodAinfBasisData_of_isPer : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]), (∀ g, IsUnit (ρ g)) → ∀ s : Seed bk d ρ τ, Nonempty (Height s) := by
  first | exact @GlobalTheory.BSP.HeightEx.nonempty_height | exact GlobalTheory.BSP.HeightEx.nonempty_height | (intros; apply GlobalTheory.BSP.HeightEx.nonempty_height <;> assumption)
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem eval_transition_comp_assoc {l : ℕ} {R : Type} [CommRing R] {P P' P'' P''' : Obj l R}
    (c : Hom P'' P''') (b : Hom P' P'') (a : Hom P P') : c.comp (b.comp a) = (c.comp b).comp a :=
  Hom.ext' rfl

theorem eval_transition : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d)
    (B B' : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (N' : Type) [AddCommGroup N']
    [Module B'.A N'] (V : Eval S B N) (V' : Eval S B' N') (k : Hom B B'),
    ∃ t : N →ₛₗ[k.f] N', SemiBC t ∧ ∀ (Q : Obj l ↥(OL K)) (a : Hom B' Q) (g : Hom bk.prism Q) (x : N),
      V'.v a g (t x) = V.v (a.comp k) g x := by
  intro l _ K bk d S B B' N _ _ N' _ _ V V' k
  obtain ⟨C', h', ⟨f'⟩, hc⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B'
  obtain ⟨hinj, hsurj⟩ := GlobalTheory.T.injective_and_range_of_prism_cover l K bk d S B' C' N' V' h' f' hc
  have hz : ∀ x : N, ∃ y, V'.v h' f' y = V.v (h'.comp k) f' x := by
    intro x
    apply hsurj
    intro Q p q hpq
    have e : p.comp (h'.comp k) = q.comp (h'.comp k) := by
      rw [eval_transition_comp_assoc, hpq, ← eval_transition_comp_assoc]
    have hp : (fun i => p.f (V.v (h'.comp k) f' x i)) = V.v (p.comp (h'.comp k)) (p.comp f') x :=
      funext fun i => (V.v_nat p (h'.comp k) f' x i).symm
    have hq : (fun i => q.f (V.v (h'.comp k) f' x i)) = V.v (q.comp (h'.comp k)) (q.comp f') x :=
      funext fun i => (V.v_nat q (h'.comp k) f' x i).symm
    rw [hp, hq, V.v_ε (p.comp (h'.comp k)) (p.comp f') (q.comp f') x, e]
  choose t0 ht0 using hz
  let t : N →ₛₗ[k.f] N' :=
    { toFun := t0
      map_add' := fun x y => hinj <|
        (ht0 (x + y)).trans ((LinearMap.map_add (V.v (h'.comp k) f') x y).trans
          ((congrArg₂ (· + ·) (ht0 x) (ht0 y)).symm.trans (LinearMap.map_add (V'.v h' f') (t0 x) (t0 y)).symm))
      map_smul' := fun c x => hinj <|
        (ht0 (c • x)).trans ((LinearMap.map_smulₛₗ (V.v (h'.comp k) f') c x).trans
          ((congrArg (h'.f (k.f c) • ·) (ht0 x)).symm.trans (LinearMap.map_smulₛₗ (V'.v h' f') (k.f c) (t0 x)).symm)) }
  have hT : ∀ x, V'.v h' f' (t x) = V.v (h'.comp k) f' x := ht0
  refine ⟨t, ?_, ?_⟩
  · haveI := V.fin; haveI := V.proj; haveI := V'.fin; haveI := V'.proj
    exact GlobalTheory.T.semilinear_projective_module_compose l (↥(OL K)) B' C' h' hc B.A k.f N N' (Fin d → C'.A) t (V'.v h' f')
      (V.v (h'.comp k) f') (fun x => (hT x).symm) (V'.bc h' f') (V.bc (h'.comp k) f')
  · intro Q a g x
    obtain ⟨Q'', h'', a', hsq, hinj''⟩ := GlobalTheory.T.exists_injective_pushout_of_prismCover l K bk d S B' C' h' hc Q a
    have e2 : h''.comp (a.comp k) = a'.comp (h'.comp k) := by
      rw [eval_transition_comp_assoc, ← hsq, ← eval_transition_comp_assoc]
    have key : V'.v (a'.comp h') (a'.comp f') (t x) = V.v (a'.comp (h'.comp k)) (a'.comp f') x :=
      funext fun j => (V'.v_nat a' h' f' (t x) j).trans ((congrArg a'.f (congrFun (hT x) j)).trans (V.v_nat a' (h'.comp k) f' x j).symm)
    funext i
    apply hinj''
    calc h''.f (V'.v a g (t x) i) = V'.v (h''.comp a) (h''.comp g) (t x) i := (V'.v_nat h'' a g (t x) i).symm
      _ = V'.v (a'.comp h') (h''.comp g) (t x) i := congrArg (fun c => V'.v c (h''.comp g) (t x) i) hsq.symm
      _ = (S.ε (h''.comp g) (a'.comp f')).mulVec (V'.v (a'.comp h') (a'.comp f') (t x)) i :=
          congrFun (V'.v_ε (a'.comp h') (h''.comp g) (a'.comp f') (t x)) i
      _ = (S.ε (h''.comp g) (a'.comp f')).mulVec (V.v (a'.comp (h'.comp k)) (a'.comp f') x) i :=
          congrArg (fun w => (S.ε (h''.comp g) (a'.comp f')).mulVec w i) key
      _ = V.v (a'.comp (h'.comp k)) (h''.comp g) x i :=
          (congrFun (V.v_ε (a'.comp (h'.comp k)) (h''.comp g) (a'.comp f') x) i).symm
      _ = V.v (h''.comp (a.comp k)) (h''.comp g) x i := congrArg (fun c => V.v c (h''.comp g) x i) e2.symm
      _ = h''.f (V.v (a.comp k) g x i) := V.v_nat h'' (a.comp k) g x i

end GlobalTheory.BSP
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stratifiedValue_transition_baseChange : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B B' : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (N' : Type) [AddCommGroup N'] [Module B'.A N'] (V : Eval S B N) (V' : Eval S B' N') (k : Hom B B'), ∃ t : N →ₛₗ[k.f] N', SemiBC t ∧ ∀ (Q : Obj l ↥(OL K)) (a : Hom B' Q) (g : Hom bk.prism Q) (x : N), V'.v a g (t x) = V.v (a.comp k) g x := by
  atlas_forward_decl GlobalTheory.BSP.eval_transition
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isFrac_transition : ∀ (A A' : Type) [CommRing A] [CommRing A'] (k : A →+* A') (N : Type) [AddCommGroup N] [Module A N] (N' : Type) [AddCommGroup N'] [Module A' N'] (τ : N →ₛₗ[k] N') (t : A) (t' : A') (a : ℕ) (y : LocalizedModule (Submonoid.powers t) N) (y' : LocalizedModule (Submonoid.powers t') N') (z m : N) (z' n : N') (i j : ℕ), IsFrac t y z a → IsFrac t y m i → IsFrac t' y' z' a → IsFrac t' y' n j → t' ^ a • τ z = k t ^ a • z' → ∃ r : ℕ, (k t * t') ^ r • (t' ^ j • τ m - k t ^ i • n) = 0 := by
  intro A A' _ _ k N _ _ N' _ _ τ t t' a y y' z m z' n i j h1 h2 h3 h4 h5
  unfold IsFrac at h1 h2 h3 h4
  obtain ⟨⟨_, r₁, rfl⟩, e1⟩ := LocalizedModule.mk_eq.1 (h1.symm.trans h2)
  obtain ⟨⟨_, r₂, rfl⟩, e2⟩ := LocalizedModule.mk_eq.1 (h3.symm.trans h4)
  simp only [Submonoid.smul_def] at e1 e2
  have e3 := congrArg τ e1
  simp only [map_smulₛₗ, map_pow] at e3
  refine ⟨r₁ + r₂ + a, ?_⟩
  linear_combination (norm := skip) (-(k t ^ r₂ * t' ^ (r₁ + r₂ + a) * t' ^ j)) • e3
    + (k t ^ (r₂ + r₁ + i) * t' ^ (r₁ + r₂ + j)) • h5
    + (k t ^ (r₁ + r₂ + a + i) * t' ^ r₁) • e2
  match_scalars <;> ring

end GlobalTheory.BSP
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocalizedFraction_semilinear_transition : ∀ (A A' : Type) [CommRing A] [CommRing A'] (k : A →+* A') (N : Type) [AddCommGroup N] [Module A N] (N' : Type) [AddCommGroup N'] [Module A' N'] (τ : N →ₛₗ[k] N') (t : A) (t' : A') (a : ℕ) (y : LocalizedModule (Submonoid.powers t) N) (y' : LocalizedModule (Submonoid.powers t') N') (z m : N) (z' n : N') (i j : ℕ), IsFrac t y z a → IsFrac t y m i → IsFrac t' y' z' a → IsFrac t' y' n j → t' ^ a • τ z = k t ^ a • z' → ∃ r : ℕ, (k t * t') ^ r • (t' ^ j • τ m - k t ^ i • n) = 0 := by
  atlas_forward_decl GlobalTheory.BSP.isFrac_transition
end

section
section
noncomputable section

open GlobalTheory.Prism

namespace GlobalTheory.BSP

def fracMap {A : Type} [CommRing A] {N P : Type} [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]
    (S : Submonoid A) (L : P →ₗ[A] N) (s : ↥S) : P →ₗ[A] LocalizedModule S N where
  toFun y := LocalizedModule.mk (L y) s
  map_add' x y := by
    rw [LocalizedModule.mk_add_mk, LocalizedModule.mk_eq]
    exact ⟨1, by simp [mul_smul]⟩
  map_smul' c x := by
    rw [map_smul, RingHom.id_apply, LocalizedModule.smul'_mk]

theorem isLocalizedModule_fracMap {A : Type} [CommRing A] (t : A) {N P : Type} [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P] (L : P →ₗ[A] N) (n : ℕ) (hk : ∀ y, L y = 0 → t ^ n • y = 0)
    (hc : ∀ x, ∃ y, L y = t ^ n • x) (s : ↥(Submonoid.powers t)) :
    IsLocalizedModule (Submonoid.powers t) (fracMap (Submonoid.powers t) L s) where
  map_units := IsLocalizedModule.map_units (LocalizedModule.mkLinearMap (Submonoid.powers t) N)
  surj z := by
    induction z using LocalizedModule.induction_on with
    | _ m r =>
      obtain ⟨y, hy⟩ := hc m
      refine ⟨⟨(s : A) • y, r * ⟨t ^ n, n, rfl⟩⟩, ?_⟩
      change ((r : A) * t ^ n) • LocalizedModule.mk m r = LocalizedModule.mk (L ((s : A) • y)) s
      rw [LocalizedModule.smul'_mk, LocalizedModule.mk_eq, map_smul, hy]
      refine ⟨1, ?_⟩
      simp only [Submonoid.smul_def, smul_smul]
      congr 1
      ring
  exists_of_eq {x y} h := by
    change LocalizedModule.mk (L x) s = LocalizedModule.mk (L y) s at h
    rw [LocalizedModule.mk_eq] at h
    obtain ⟨c, h⟩ := h
    refine ⟨⟨t ^ n, n, rfl⟩ * (c * s), ?_⟩
    have h1 := hk (((c : A) * s) • (x - y)) (by
      rw [map_smul, map_sub, smul_sub, sub_eq_zero, mul_smul, mul_smul]
      exact h)
    rw [smul_smul, smul_sub, sub_eq_zero] at h1
    exact h1

theorem semiBC_localized (A : Type) [CommRing A] (φ : A →+* A) (t : A) (N : Type) [AddCommGroup N] [Module A N]
    (P : Type) [AddCommGroup P] [Module A P] (u : N →ₛₗ[φ] P) (hu : SemiBC u) (L : P →ₗ[A] N) (n a : ℕ)
    (hk : ∀ y, L y = 0 → t ^ n • y = 0) (hc : ∀ x, ∃ y, L y = t ^ n • x)
    (Φ : N →ₛₗ[(algebraMap A (Localization.Away t)).comp φ] LocalizedModule (Submonoid.powers t) N)
    (hΦ : ∀ x, IsFrac t (Φ x) (L (u x)) a) : SemiBC Φ := by
  intro Q _ _ v
  letI : Module A Q := Module.compHom Q (algebraMap A (Localization.Away t))
  haveI : IsScalarTower A (Localization.Away t) Q := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let s : ↥(Submonoid.powers t) := ⟨t ^ a, a, rfl⟩
  haveI := isLocalizedModule_fracMap t L n hk hc s
  have hb := IsLocalizedModule.isBaseChange (Submonoid.powers t) (Localization.Away t)
    (fracMap (Submonoid.powers t) L s)
  have hΦ' : ∀ x, Φ x = fracMap (Submonoid.powers t) L s (u x) := hΦ
  let v' : N →ₛₗ[φ] Q :=
    { toFun := v
      map_add' := v.map_add
      map_smul' := fun c x => v.map_smulₛₗ c x }
  obtain ⟨w₀, hw₀, hun⟩ := hu Q v'
  refine ⟨hb.lift w₀, fun x => ?_, fun w hw => ?_⟩
  · rw [hΦ', hb.lift_eq]
    exact hw₀ x
  · refine hb.algHom_ext _ _ fun y => ?_
    rw [hb.lift_eq, ← hun ((w.restrictScalars A).comp (fracMap (Submonoid.powers t) L s))
      fun x => (congrArg w (hΦ' x).symm).trans (hw x)]
    rfl

end GlobalTheory.BSP
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSemilinearBaseChange_localized_of_torsion_bounded : ∀ (A : Type) [CommRing A] (φ : A →+* A) (t : A) (N : Type) [AddCommGroup N] [Module A N] (P : Type) [AddCommGroup P] [Module A P] (u : N →ₛₗ[φ] P), SemiBC u → ∀ (L : P →ₗ[A] N) (n a : ℕ), (∀ y, L y = 0 → t ^ n • y = 0) → (∀ x, ∃ y, L y = t ^ n • x) → ∀ Φ : N →ₛₗ[(algebraMap A (Localization.Away t)).comp φ] LocalizedModule (Submonoid.powers t) N, (∀ x, IsFrac t (Φ x) (L (u x)) a) → SemiBC Φ := by
  atlas_forward_decl GlobalTheory.BSP.semiBC_localized
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.FrobValue

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ}

theorem hf_comp {Q Q' : Obj l ↥(OL K)} (c : Hom Q Q') (g : Hom bk.prism Q) :
    BK.hf (c.comp g) = c.f.comp (BK.hf g) := rfl

theorem frob_change (S : Strat bk d) {Q : Obj l ↥(OL K)} (g g' : Hom bk.prism Q) (y y' : Fin d → Q.A)
    (hy : y = (S.ε g g').mulVec y') :
    BK.hf g' bk.E ^ S.a • (S.A.map (BK.hf g)).mulVec (fun i => Q.D.φ (y i)) =
      BK.hf g bk.E ^ S.a • (S.ε g g').mulVec ((S.A.map (BK.hf g')).mulVec (fun i => Q.D.φ (y' i))) := by
  have e : (fun i => Q.D.φ (y i)) = ((S.ε g g').map Q.D.φ).mulVec (fun i => Q.D.φ (y' i)) := by
    funext i; rw [hy, RingHom.map_mulVec]; rfl
  rw [e, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.smul_mulVec, ← Matrix.smul_mulVec,
    S.ε_φ]

theorem push (S : Strat bk d) {C Q : Obj l ↥(OL K)} (p : Hom C Q) (f : Hom bk.prism C) (c : C.A)
    (y : Fin d → C.A) :
    (fun i => p.f ((c ^ S.a • (S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (y j))) i)) =
      p.f c ^ S.a • (S.A.map (BK.hf (p.comp f))).mulVec (fun j => Q.D.φ (p.f (y j))) := by
  funext i
  have h1 : p.f ((c ^ S.a • (S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (y j))) i) =
      p.f c ^ S.a * p.f ((S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (y j)) i) := by
    rw [Pi.smul_apply, smul_eq_mul, map_mul, map_pow]
  have h2 : p.f ((S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (y j)) i) =
      (S.A.map (BK.hf (p.comp f))).mulVec (fun j => Q.D.φ (p.f (y j))) i := by
    rw [RingHom.map_mulVec, Matrix.map_map, hf_comp]
    congr 1
    funext j
    exact p.f_φ (y j)
  refine h1.trans ?_
  simp only [h2, Pi.smul_apply, smul_eq_mul]

theorem vec_cancel {A : Type} [CommRing A] {r : A} (hr : r ∈ nonZeroDivisors A) {u w : Fin d → A}
    (e : r • u = r • w) : u = w :=
  funext fun i => (mul_cancel_left_mem_nonZeroDivisors hr).1 (congrFun e i)

theorem pow_smul_transfer_of_regular {A : Type} [CommRing A] {a : ℕ} {e e' u u' : A} {L R : Fin d → A}
    (hr : e ^ a * e' ^ a ∈ nonZeroDivisors A) (hF : e' ^ a • L = e ^ a • R) (hT : u * e = u' * e') :
    u ^ a • L = u' ^ a • R := by
  refine vec_cancel hr ?_
  calc (e ^ a * e' ^ a) • (u ^ a • L) = (u * e) ^ a • (e' ^ a • L) := by
        rw [smul_smul, smul_smul, mul_pow]; congr 1; ring
    _ = (u' * e') ^ a • (e ^ a • R) := by rw [hF, hT]
    _ = (e ^ a * e' ^ a) • (u' ^ a • R) := by
        rw [smul_smul, smul_smul, mul_pow]; congr 1; ring

theorem compat (S : Strat bk d) {B C Q : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N]
    (V : Eval S B N) (h : Hom B C) (f : Hom bk.prism C) (c : C.A) (t : B.A) (hc : c * BK.hf f bk.E = h.f t)
    (hn : ∀ g : Hom bk.prism Q, BK.hf g bk.E ∈ nonZeroDivisors Q.A)
    (x : N) (p q : Hom C Q) (hpq : p.comp h = q.comp h) :
    (fun i => p.f ((c ^ S.a • (S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (V.v h f x j))) i)) =
      (S.ε (p.comp f) (q.comp f)).mulVec
        (fun i => q.f ((c ^ S.a • (S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (V.v h f x j))) i)) := by
  have hY : ∀ j, p.f (V.v h f x j) = V.v (p.comp h) (p.comp f) x j :=
    fun j => (V.v_nat p h f x j).symm
  have hY' : ∀ j, q.f (V.v h f x j) = V.v (p.comp h) (q.comp f) x j := by
    rw [hpq]; exact fun j => (V.v_nat q h f x j).symm
  have hF := frob_change S (p.comp f) (q.comp f) _ _ (V.v_ε (p.comp h) (p.comp f) (q.comp f) x)
  have hT : p.f c * BK.hf (p.comp f) bk.E = q.f c * BK.hf (q.comp f) bk.E := by
    have e1 : p.f (c * BK.hf f bk.E) = q.f (c * BK.hf f bk.E) := by
      rw [hc]; exact congrArg (fun k : Hom B Q => k.f t) hpq
    simpa only [map_mul, hf_comp, RingHom.comp_apply] using e1
  rw [push S p f c, push S q f c, Matrix.mulVec_smul]
  simp only [hY, hY']
  exact pow_smul_transfer_of_regular (mul_mem (pow_mem (hn (p.comp f)) S.a) (pow_mem (hn (q.comp f)) S.a)) hF hT

theorem pow_smul_matrix_swap_of_relation {A : Type} [CommRing A] {a : ℕ} {e e' u : A} {L M : Fin d → A} {P : Matrix (Fin d) (Fin d) A}
    (hF : e' ^ a • L = e ^ a • P.mulVec M) : e ^ a • P.mulVec (u ^ a • M) = (u * e') ^ a • L := by
  rw [Matrix.mulVec_smul, mul_pow, mul_smul, hF, smul_comm]

theorem coord (S : Strat bk d) {B C Q Q' : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N]
    (V : Eval S B N) (h : Hom B C) (f : Hom bk.prism C) (c : C.A) (t : B.A) (hc : c * BK.hf f bk.E = h.f t)
    (a : Hom B Q) (g : Hom bk.prism Q) (h' : Hom Q Q') (a' : Hom C Q') (hcomm : a'.comp h = h'.comp a)
    (hinj' : Function.Injective h'.f) (x w : N)
    (hw : V.v h f w = c ^ S.a • (S.A.map (BK.hf f)).mulVec (fun i => C.D.φ (V.v h f x i))) :
    BK.hf g bk.E ^ S.a • V.v a g w = a.f t ^ S.a • (S.A.map (BK.hf g)).mulVec fun i => Q.D.φ (V.v a g x i) := by
  have nat' : ∀ (y : N) j, h'.f (V.v a g y j) = V.v (a'.comp h) (h'.comp g) y j := by
    intro y j; rw [hcomm]; exact (V.v_nat h' a g y j).symm
  have natC : ∀ (y : N) j, a'.f (V.v h f y j) = V.v (a'.comp h) (a'.comp f) y j :=
    fun y j => (V.v_nat a' h f y j).symm
  have ht : h'.f (a.f t) = a'.f c * BK.hf (a'.comp f) bk.E := by
    have e : h'.f (a.f t) = a'.f (h.f t) := congrArg (fun k : Hom B Q' => k.f t) hcomm.symm
    rw [e, ← hc, map_mul]; rfl
  have e1 : (fun i => h'.f ((BK.hf g bk.E ^ S.a • V.v a g w) i)) =
      BK.hf (h'.comp g) bk.E ^ S.a • V.v (a'.comp h) (h'.comp g) w := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow, nat']
    rfl
  have e2 : V.v (a'.comp h) (a'.comp f) w =
      a'.f c ^ S.a • (S.A.map (BK.hf (a'.comp f))).mulVec fun j => Q'.D.φ (V.v (a'.comp h) (a'.comp f) x j) := by
    have e := push S a' f c (V.v h f x)
    rw [← hw] at e
    simp only [natC] at e
    exact e
  have e3 := push S h' g (a.f t) (V.v a g x)
  simp only [nat', ht] at e3
  have hF := frob_change S (h'.comp g) (a'.comp f) _ _ (V.v_ε (a'.comp h) (h'.comp g) (a'.comp f) x)
  have key : (fun i => h'.f ((BK.hf g bk.E ^ S.a • V.v a g w) i)) =
      fun i => h'.f ((a.f t ^ S.a • (S.A.map (BK.hf g)).mulVec fun j => Q.D.φ (V.v a g x j)) i) := by
    have v1 := (V.v_ε (a'.comp h) (h'.comp g) (a'.comp f) w).trans (congrArg _ e2)
    exact e1.trans ((congrArg (fun v => BK.hf (h'.comp g) bk.E ^ S.a • v) v1).trans ((pow_smul_matrix_swap_of_relation hF).trans e3.symm))
  funext i
  exact hinj' (congrFun key i)

theorem psi_exists : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d)
    (B : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (V : Eval S B N) (t : B.A), t ∈ B.I →
    ∃ Ψ : N →ₛₗ[B.D.φ] N, IsPsi V t Ψ := by
  intro l _ K bk d S B N _ _ V t ht
  obtain ⟨C, h, ⟨f⟩, hC⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B
  have hIC := (GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk C f).1
  have htC : h.f t ∈ Ideal.span {BK.hf f bk.E} := hIC ▸ h.f_I t ht
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 htC
  obtain ⟨hinj, hsurj⟩ := GlobalTheory.T.injective_and_range_of_prism_cover l K bk d S B C N V h f hC
  have hzc : ∀ x : N, ∃ y, V.v h f y = c ^ S.a • (S.A.map (BK.hf f)).mulVec (fun i => C.D.φ (V.v h f x i)) :=
    fun x => hsurj _ fun Q p q hpq =>
      compat S V h f c t hc (fun g => (GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk Q g).2) x p q hpq
  choose Ψf hΨf using hzc
  have zadd : ∀ x y : N, Ψf (x + y) = Ψf x + Ψf y := by
    intro x y
    apply hinj
    have e1 : V.v h f (x + y) = V.v h f x + V.v h f y := map_add (V.v h f) x y
    have e2 : V.v h f (Ψf x + Ψf y) = V.v h f (Ψf x) + V.v h f (Ψf y) := map_add (V.v h f) _ _
    have hφ : (fun i => C.D.φ (V.v h f (x + y) i)) =
        (fun i => C.D.φ (V.v h f x i)) + (fun i => C.D.φ (V.v h f y i)) :=
      funext fun i => (congrArg (fun v : Fin d → C.A => C.D.φ (v i)) e1).trans (C.D.φ.map_add _ _)
    refine (hΨf (x + y)).trans (Eq.trans ?_ ((congrArg₂ (· + ·) (hΨf x) (hΨf y)).symm.trans e2.symm))
    refine (congrArg (fun v => c ^ S.a • (S.A.map (BK.hf f)).mulVec v) hφ).trans ?_
    exact (congrArg (c ^ S.a • ·) (Matrix.mulVec_add _ _ _)).trans (smul_add _ _ _)
  have zsmul : ∀ (b : B.A) (x : N), Ψf (b • x) = B.D.φ b • Ψf x := by
    intro b x
    apply hinj
    have e1 : V.v h f (b • x) = h.f b • V.v h f x := LinearMap.map_smulₛₗ (V.v h f) b x
    have e2 : V.v h f (B.D.φ b • Ψf x) = h.f (B.D.φ b) • V.v h f (Ψf x) := LinearMap.map_smulₛₗ (V.v h f) _ _
    have hφ : (fun i => C.D.φ (V.v h f (b • x) i)) = h.f (B.D.φ b) • (fun i => C.D.φ (V.v h f x i)) :=
      funext fun i => (congrArg (fun v : Fin d → C.A => C.D.φ (v i)) e1).trans
        ((C.D.φ.map_mul _ _).trans (congrArg (· * C.D.φ (V.v h f x i)) (h.f_φ b).symm))
    refine (hΨf (b • x)).trans (Eq.trans ?_ ((congrArg (h.f (B.D.φ b) • ·) (hΨf x)).symm.trans e2.symm))
    refine (congrArg (fun v => c ^ S.a • (S.A.map (BK.hf f)).mulVec v) hφ).trans ?_
    exact (congrArg (c ^ S.a • ·) (Matrix.mulVec_smul _ _ _)).trans (smul_comm _ _ _)
  refine ⟨{ toFun := Ψf, map_add' := zadd, map_smul' := zsmul }, ?_⟩
  intro Q a g x
  obtain ⟨Q', h', a', hcomm, hinj'⟩ := GlobalTheory.T.exists_injective_pushout_of_prismCover l K bk d S B C h hC Q a
  exact coord S V h f c t hc a g h' a' hcomm hinj' x (Ψf x) (hΨf x)

end GlobalTheory.BSP.FrobValue
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobenius_on_stratifiedValue : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (V : Eval S B N) (t : B.A), t ∈ B.I → ∃ Ψ : N →ₛₗ[B.D.φ] N, IsPsi V t Ψ := by
  atlas_forward_decl GlobalTheory.BSP.FrobValue.psi_exists
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.BSP.psi_nat : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B B' : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (N' : Type) [AddCommGroup N'] [Module B'.A N'] (V : Eval S B N) (V' : Eval S B' N') (k : Hom B B') (τ : N →ₛₗ[k.f] N'), (∀ (Q : Obj l ↥(OL K)) (a : Hom B' Q) (g : Hom bk.prism Q) (x : N), V'.v a g (τ x) = V.v (a.comp k) g x) → ∀ (t : B.A) (t' : B'.A) (Ψ : N →ₛₗ[B.D.φ] N) (Ψ' : N' →ₛₗ[B'.D.φ] N'), IsPsi V t Ψ → IsPsi V' t' Ψ' → ∀ x, t' ^ S.a • τ (Ψ x) = k.f t ^ S.a • Ψ' (τ x) := by
  intro l _ K bk d S B B' N _ _ N' _ _ V V' k τ hτ t t' Ψ Ψ' hΨ hΨ' x
  obtain ⟨C, h, ⟨f⟩, hc⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B'
  have hinj := (GlobalTheory.T.injective_and_range_of_prism_cover l K bk d S B' C N' V' h f hc).1
  have hE : BK.hf f bk.E ^ S.a ∈ nonZeroDivisors C.A := pow_mem (GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk C f).2 _
  apply hinj
  have L : V'.v h f (t' ^ S.a • τ (Ψ x)) = h.f t' ^ S.a • V.v (h.comp k) f (Ψ x) := by
    rw [map_smulₛₗ, map_pow, hτ]
  have R : V'.v h f (k.f t ^ S.a • Ψ' (τ x)) = h.f (k.f t) ^ S.a • V'.v h f (Ψ' (τ x)) := by
    rw [map_smulₛₗ, map_pow]
  have hkt : (h.comp k).f t = h.f (k.f t) := rfl
  have key : BK.hf f bk.E ^ S.a • V'.v h f (t' ^ S.a • τ (Ψ x)) =
      BK.hf f bk.E ^ S.a • V'.v h f (k.f t ^ S.a • Ψ' (τ x)) := by
    rw [L, R, smul_comm (BK.hf f bk.E ^ S.a) (h.f t' ^ S.a), smul_comm (BK.hf f bk.E ^ S.a) (h.f (k.f t) ^ S.a),
      hΨ (h.comp k) f x, hΨ' h f (τ x), hτ C h f x, smul_smul, smul_smul, hkt, mul_comm]
  funext i
  have hi := congrFun key i
  simp only [Pi.smul_apply, smul_eq_mul] at hi
  exact (mul_cancel_left_mem_nonZeroDivisors hE).1 hi
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stratifiedValue_frobenius_comm_transition : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B B' : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (N' : Type) [AddCommGroup N'] [Module B'.A N'] (V : Eval S B N) (V' : Eval S B' N') (k : Hom B B') (τ : N →ₛₗ[k.f] N'), (∀ (Q : Obj l ↥(OL K)) (a : Hom B' Q) (g : Hom bk.prism Q) (x : N), V'.v a g (τ x) = V.v (a.comp k) g x) → ∀ (t : B.A) (t' : B'.A) (Ψ : N →ₛₗ[B.D.φ] N) (Ψ' : N' →ₛₗ[B'.D.φ] N'), IsPsi V t Ψ → IsPsi V' t' Ψ' → ∀ x, t' ^ S.a • τ (Ψ x) = k.f t ^ S.a • Ψ' (τ x) := by
  atlas_forward_decl GlobalTheory.BSP.psi_nat
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.LinFrob

open scoped Matrix

section Algebra

variable {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
  {f : A →+* B} {u : M →ₛₗ[f] N}

theorem span_range_eq_top (h : SemiBC u) : Submodule.span B (Set.range u) = ⊤ := by
  obtain ⟨w, -, hw⟩ := h (N ⧸ Submodule.span B (Set.range u)) 0
  have h1 := hw (Submodule.mkQ _) fun x =>
    (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span ⟨x, rfl⟩)
  have h2 := hw 0 fun _ => rfl
  rw [← Submodule.ker_mkQ (Submodule.span B (Set.range u)), h1, ← h2, LinearMap.ker_zero]

theorem induction_bc (h : SemiBC u) (p : N → Prop) (h0 : ∀ x, p (u x)) (h1 : ∀ y z, p y → p z → p (y + z))
    (h2 : ∀ (b : B) y, p y → p (b • y)) (y : N) : p y := by
  have hy : y ∈ Submodule.span B (Set.range u) := by rw [span_range_eq_top h]; trivial
  induction hy using Submodule.span_induction with
  | mem _ hx => obtain ⟨x, rfl⟩ := hx; exact h0 x
  | zero => rw [← map_zero u]; exact h0 0
  | add y z _ _ hy hz => exact h1 y z hy hz
  | smul b y _ hy => exact h2 b y hy

theorem exists_ext {C P : Type} [CommRing C] [AddCommGroup P] [Module C P] (h : SemiBC u) (τ : B →+* C)
    (w : M →+ P) (hw : ∀ (a : A) x, w (a • x) = τ (f a) • w x) :
    ∃ κ : N →ₛₗ[τ] P, ∀ x, κ (u x) = w x := by
  letI : Module B P := Module.compHom P τ
  obtain ⟨W, hW, -⟩ := h P { toFun := w, map_add' := w.map_add, map_smul' := fun a x => hw a x }
  exact ⟨{ toFun := W, map_add' := W.map_add, map_smul' := fun b y => W.map_smul b y }, hW⟩

theorem semiBC_cancel {C P : Type} [CommRing C] [AddCommGroup P] [Module C P] {τ : B →+* C} {ρ : A →+* C}
    (h : SemiBC u) {w : M →ₛₗ[ρ] P} (hw : SemiBC w) (hρ : ∀ a, ρ a = τ (f a)) (κ : N →ₛₗ[τ] P)
    (hκ : ∀ x, κ (u x) = w x) : SemiBC κ := by
  intro Q _ _ m
  obtain ⟨W, hW, hU⟩ := hw Q
    { toFun := fun x => m (u x)
      map_add' := fun x y => by rw [map_add, map_add]
      map_smul' := fun a x => by rw [u.map_smulₛₗ, m.map_smulₛₗ, hρ] }
  refine ⟨W, fun y => ?_, fun W' hW' => hU W' fun x => by rw [← hκ]; exact hW' (u x)⟩
  refine induction_bc h (fun y => W (κ y) = m y) (fun x => ?_) (fun y z hy hz => ?_) (fun b y hy => ?_) y
  · show W (κ (u x)) = m (u x)
    rw [hκ]; exact hW x
  · show W (κ (y + z)) = m (y + z)
    rw [map_add, map_add, map_add, hy, hz]
  · show W (κ (b • y)) = m (b • y)
    rw [κ.map_smulₛₗ, W.map_smul, m.map_smulₛₗ, hy]

def Tw {Q : Type} [CommRing Q] (_σ : Q →+* Q) (Q' : Type) : Type := Q'

instance Tw.addCommGroup {Q Q' : Type} [CommRing Q] [AddCommGroup Q'] (σ : Q →+* Q) : AddCommGroup (Tw σ Q') :=
  inferInstanceAs (AddCommGroup Q')

instance Tw.module {Q Q' : Type} [CommRing Q] [AddCommGroup Q'] [Module Q Q'] (σ : Q →+* Q) : Module Q (Tw σ Q') :=
  Module.compHom Q' σ

theorem semiBC_frob {Q : Type} [CommRing Q] {d : ℕ} {α β : B →+* Q} (σ : Q →+* Q) (hβ : ∀ b, β b = σ (α b))
    {V : N →ₛₗ[α] (Fin d → Q)} (hV : SemiBC V) (w : N →ₛₗ[β] (Fin d → Q)) (hw : ∀ x i, w x i = σ (V x i)) :
    SemiBC w := by
  intro Q' _ _ m
  obtain ⟨W₁, hW₁, hU₁⟩ := hV (Tw σ Q')
    { toFun := fun x => (m x : Tw σ Q')
      map_add' := fun x y => map_add m x y
      map_smul' := fun b x => by
        show m (b • x) = σ (α b) • m x
        rw [m.map_smulₛₗ, hβ] }
  let e : Fin d → Q' := fun i => (W₁ (Pi.single i 1) : Q')
  have he : ∀ z : Fin d → Q, (W₁ z : Q') = ∑ i, σ (z i) • e i := fun z => by
    conv_lhs => rw [pi_eq_sum_univ' z]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => W₁.map_smul (z i) (Pi.single i 1)
  refine ⟨Fintype.linearCombination Q e, fun x => ?_, fun W' hW' => ?_⟩
  · rw [Fintype.linearCombination_apply]
    have h1 := he (V x)
    have h2 : (W₁ (V x) : Q') = m x := hW₁ x
    rw [h2] at h1
    rw [h1]
    exact Finset.sum_congr rfl fun i _ => by rw [hw]
  · let W'' : (Fin d → Q) →ₗ[Q] Tw σ Q' :=
      { toFun := fun z => (W' (fun i => σ (z i)) : Tw σ Q')
        map_add' := fun z z' => by
          show W' (fun i => σ ((z + z') i)) = W' (fun i => σ (z i)) + W' (fun i => σ (z' i))
          rw [← map_add]; congr 1; funext i; simp
        map_smul' := fun c z => by
          show W' (fun i => σ ((c • z) i)) = σ c • W' (fun i => σ (z i))
          rw [← map_smul]; congr 1; funext i; simp }
    have h1 : W'' = W₁ := hU₁ W'' fun x => by
      show W' (fun i => σ (V x i)) = m x
      rw [← hW' x]; congr 1; funext i; rw [hw]
    refine LinearMap.pi_ext fun i c => ?_
    rw [Fintype.linearCombination_apply_single]
    have h2 : Pi.single i c = c • (Pi.single i (1 : Q) : Fin d → Q) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [h2, map_smul]
    congr 1
    have h3 : (W'' (Pi.single i 1) : Q') = W' (Pi.single i 1) := by
      show W' (fun j => σ ((Pi.single i (1 : Q) : Fin d → Q) j)) = W' (Pi.single i 1)
      congr 1; funext j; by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_apply, hj]
    rw [← h3, h1]

end Algebra

theorem smul_cancel_nzd {R n : Type} [CommRing R] {e : R} (he : e ∈ nonZeroDivisors R) {v w : n → R}
    (h : e • v = e • w) : v = w :=
  funext fun i => (mul_cancel_left_mem_nonZeroDivisors he).1 (congrFun h i)

theorem mul_pow_smul {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (c e : R) (a : ℕ) (v : M) :
    (c * e) ^ a • v = e ^ a • c ^ a • v := by
  rw [mul_pow, mul_comm, mul_smul]

theorem ker_gen {R n : Type} [CommRing R] [Fintype n] [DecidableEq n] {A A' : Matrix n n R} {E c : R} {a b : ℕ}
    (hA : A' * A = E ^ b • 1) {v : n → R} (h : c ^ a • (A *ᵥ v) = 0) : (c * E) ^ (a + b) • v = 0 := by
  have h2 := congrArg (fun w => A' *ᵥ w) h
  simp only [Matrix.mulVec_zero, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hA, Matrix.smul_mulVec,
    Matrix.one_mulVec, smul_smul] at h2
  rw [show (c * E) ^ (a + b) = (c ^ b * E ^ a) * (c ^ a * E ^ b) by ring, mul_smul, h2, smul_zero]

theorem img_gen {R n : Type} [CommRing R] [Fintype n] [DecidableEq n] {A A' : Matrix n n R} {E c T : R} {a b : ℕ}
    (hA : A * A' = E ^ b • 1) (hT : T = c * E) (v : n → R) :
    c ^ a • (A *ᵥ ((T ^ (a + b) * (E ^ a * c ^ b)) • (A' *ᵥ v))) = T ^ (2 * (a + b)) • v := by
  subst hT
  simp only [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hA, Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul]
  congr 1
  ring

theorem smul_pow_two_mul {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {t : R} {n : ℕ} {y : M}
    (h : t ^ n • y = 0) : t ^ (2 * n) • y = 0 := by
  rw [two_mul, pow_add, mul_smul, h, smul_zero]

def piMap {R R' n : Type} [CommRing R] [CommRing R'] (g : R →+* R') : (n → R) →ₛₗ[g] (n → R') where
  toFun z i := g (z i)
  map_add' z z' := funext fun i => map_add g _ _
  map_smul' r z := funext fun i => map_mul g _ _

theorem piMap_apply {R R' n : Type} [CommRing R] [CommRing R'] (g : R →+* R') (z : n → R) :
    piMap g z = fun i => g (z i) := rfl

def piMapMul {R R' n : Type} [CommRing R] [CommRing R'] [Fintype n] (g : R →+* R') (M : Matrix n n R') :
    (n → R) →ₛₗ[g] (n → R') where
  toFun z := M *ᵥ (fun i => g (z i))
  map_add' z z' := by
    rw [← Matrix.mulVec_add]; congr 1; funext i; simp
  map_smul' r z := by
    rw [← Matrix.mulVec_smul]; congr 1; funext i; simp

theorem piMapMul_apply {R R' n : Type} [CommRing R] [CommRing R'] [Fintype n] (g : R →+* R') (M : Matrix n n R')
    (z : n → R) : piMapMul g M z = M *ᵥ (fun i => g (z i)) := rfl

theorem mul_eq_smul_comm {R n : Type} [CommRing R] [Fintype n] [DecidableEq n] {X Y : Matrix n n R} {s : R}
    (hs : s ∈ nonZeroDivisors R) (h : X * Y = s • 1) : Y * X = s • 1 := by
  have hd : X.det * Y.det = s ^ Fintype.card n := by
    rw [← Matrix.det_mul, h, Matrix.det_smul, Matrix.det_one, mul_one]
  have h1 : X * (Y * X - s • 1) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul,
      sub_self]
  have h2 : X.det • (Y * X - s • 1) = 0 := by
    have h5 : X.adjugate * (X * (Y * X - s • 1)) = X.det • (Y * X - s • 1) := by
      rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
    rw [← h5, h1, Matrix.mul_zero]
  rw [← sub_eq_zero]
  ext i j
  have h3 := congrFun (congrFun h2 i) j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h3 ⊢
  have h4 : s ^ Fintype.card n * (Y * X - s • 1) i j = s ^ Fintype.card n * 0 := by
    rw [← hd]; linear_combination Y.det * h3
  exact (mul_cancel_left_mem_nonZeroDivisors (pow_mem hs _)).1 h4

theorem descent_identity {R n : Type} [CommRing R] [Fintype n] [DecidableEq n] (Ap A'p Aq A'q ε φε : Matrix n n R)
    (Ep Eq cp cq : R) (a b : ℕ) (w : n → R) (h1 : A'p * Ap = Ep ^ b • 1) (h2 : Aq * A'q = Eq ^ b • 1)
    (h3 : Ap * A'p = Ep ^ b • 1) (hφ : Eq ^ a • (Ap * φε) = Ep ^ a • (ε * Aq)) (hT : cp * Ep = cq * Eq) :
    ((cp * Ep) ^ (a + b) * (Ep ^ a * cp ^ b)) • (A'p *ᵥ (ε *ᵥ w)) =
      φε *ᵥ (((cq * Eq) ^ (a + b) * (Eq ^ a * cq ^ b)) • (A'q *ᵥ w)) := by
  have e1 : Ap * ((Ep ^ a * cp ^ b) • (A'p * ε)) = (Ep ^ a * cp ^ b * Ep ^ b) • ε := by
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, h3, Matrix.smul_mul, Matrix.one_mul, smul_smul]
  have e2 : Ap * ((Eq ^ a * cq ^ b) • (φε * A'q)) = (cq ^ b * Ep ^ a * Eq ^ b) • ε := by
    have : Ap * ((Eq ^ a * cq ^ b) • (φε * A'q)) = cq ^ b • ((Eq ^ a • (Ap * φε)) * A'q) := by
      rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc, mul_comm (Eq ^ a)]
    rw [this, hφ, Matrix.smul_mul, Matrix.mul_assoc, h2, Matrix.mul_smul, Matrix.mul_one, smul_smul, smul_smul,
      mul_assoc]
  have e3 : Ap * ((Ep ^ a * cp ^ b) • (A'p * ε) - (Eq ^ a * cq ^ b) • (φε * A'q)) = 0 := by
    rw [Matrix.mul_sub, e1, e2, ← sub_smul]
    have : Ep ^ a * cp ^ b * Ep ^ b - cq ^ b * Ep ^ a * Eq ^ b = Ep ^ a * ((cp * Ep) ^ b - (cq * Eq) ^ b) := by ring
    rw [this, hT, sub_self, mul_zero, zero_smul]
  have e4 : (cp * Ep) ^ (a + b) • ((Ep ^ a * cp ^ b) • (A'p * ε) - (Eq ^ a * cq ^ b) • (φε * A'q)) = 0 := by
    have : (cp * Ep) ^ (a + b) • ((Ep ^ a * cp ^ b) • (A'p * ε) - (Eq ^ a * cq ^ b) • (φε * A'q)) =
        (cp ^ (a + b) * Ep ^ a) • (A'p * (Ap * ((Ep ^ a * cp ^ b) • (A'p * ε) - (Eq ^ a * cq ^ b) • (φε * A'q)))) := by
      rw [← Matrix.mul_assoc, h1, Matrix.smul_mul, Matrix.one_mul, smul_smul]; congr 1; ring
    rw [this, e3, Matrix.mul_zero, smul_zero]
  rw [smul_sub, sub_eq_zero, smul_smul, smul_smul] at e4
  have l1 : ((cp * Ep) ^ (a + b) * (Ep ^ a * cp ^ b)) • (A'p *ᵥ (ε *ᵥ w)) =
      (((cp * Ep) ^ (a + b) * (Ep ^ a * cp ^ b)) • (A'p * ε)) *ᵥ w := by
    rw [Matrix.smul_mulVec, Matrix.mulVec_mulVec]
  have l2 : φε *ᵥ (((cq * Eq) ^ (a + b) * (Eq ^ a * cq ^ b)) • (A'q *ᵥ w)) =
      (((cp * Ep) ^ (a + b) * (Eq ^ a * cq ^ b)) • (φε * A'q)) *ᵥ w := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.smul_mulVec, hT]
  rw [l1, l2, e4]

end GlobalTheory.BSP.LinFrob

namespace GlobalTheory.BSP.LinFrob

open scoped Matrix

theorem map_A_mul {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ} (S : Strat bk d) {R : Type} [CommRing R]
    (g : bk.S →+* R) : S.A.map g * S.A'.map g = g bk.E ^ S.b • (1 : Matrix (Fin d) (Fin d) R) := by
  rw [← Matrix.map_mul, S.A_mul]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem exists_kappa {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ} {S : Strat bk d}
    {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N] (V : Eval S B N) {P : Type} [AddCommGroup P]
    [Module B.A P] {u : N →ₛₗ[B.D.φ] P} (hu : SemiBC u) {Q : Obj l ↥(OL K)} (a : Hom B Q) (g : Hom bk.prism Q) :
    ∃ κ : P →ₛₗ[a.f] (Fin d → Q.A), SemiBC κ ∧ ∀ x i, κ (u x) i = Q.D.φ (V.v a g x i) := by
  let w : N →ₛₗ[a.f.comp B.D.φ] (Fin d → Q.A) :=
    { toFun := fun x i => Q.D.φ (V.v a g x i)
      map_add' := fun x y => funext fun i => by simp
      map_smul' := fun b x => funext fun i => by
        simp [(V.v a g).map_smulₛₗ, a.f_φ] }
  have hw : SemiBC w := semiBC_frob Q.D.φ (fun b => a.f_φ b) (V.bc a g) w fun _ _ => rfl
  obtain ⟨κ, hκ⟩ := exists_ext hu a.f w.toAddMonoidHom fun b x => w.map_smulₛₗ b x
  exact ⟨κ, semiBC_cancel hu hw (fun _ => rfl) κ hκ, fun x i => by rw [hκ]; rfl⟩

theorem map_smul_mulVec {R R' n : Type} [CommRing R] [CommRing R'] [Fintype n] (g : R →+* R') (s : R)
    (M : Matrix n n R) (v : n → R) :
    (fun i => g ((s • (M *ᵥ v)) i)) = g s • ((M.map g) *ᵥ (fun i => g (v i))) := by
  funext i
  rw [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.map_mulVec]
  rfl

theorem descent_compat {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ} (S : Strat bk d)
    {C D : Obj l ↥(OL K)} (f : Hom bk.prism C) (p q : Hom C D) (c T : C.A) (hT : p.f T = q.f T)
    (hc : c * BK.hf f bk.E = T) (v : Fin d → C.A)
    (hv : (fun i => p.f (v i)) = S.ε (p.comp f) (q.comp f) *ᵥ (fun j => q.f (v j))) :
    (fun i => p.f (((T ^ (S.a + S.b) * (BK.hf f bk.E ^ S.a * c ^ S.b)) • ((S.A'.map (BK.hf f)) *ᵥ v)) i)) =
      ((S.ε (p.comp f) (q.comp f)).map D.D.φ) *ᵥ
        (fun i => q.f (((T ^ (S.a + S.b) * (BK.hf f bk.E ^ S.a * c ^ S.b)) • ((S.A'.map (BK.hf f)) *ᵥ v)) i)) := by
  subst hc
  have hEp := (GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk D (p.comp f)).2
  have hT' : p.f c * BK.hf (p.comp f) bk.E = q.f c * BK.hf (q.comp f) bk.E :=
    (map_mul p.f c _).symm.trans (hT.trans (map_mul q.f c _))
  have key := descent_identity (S.A.map (BK.hf (p.comp f))) (S.A'.map (BK.hf (p.comp f)))
    (S.A.map (BK.hf (q.comp f))) (S.A'.map (BK.hf (q.comp f))) (S.ε (p.comp f) (q.comp f))
    ((S.ε (p.comp f) (q.comp f)).map D.D.φ) _ _ (p.f c) (q.f c) S.a S.b (fun j => q.f (v j))
    (mul_eq_smul_comm (pow_mem hEp S.b) (map_A_mul S _)) (map_A_mul S _) (map_A_mul S _)
    (S.ε_φ (p.comp f) (q.comp f)) hT'
  have hmp : (S.A'.map (BK.hf f)).map p.f = S.A'.map (BK.hf (p.comp f)) := Matrix.map_map
  have hmq : (S.A'.map (BK.hf f)).map q.f = S.A'.map (BK.hf (q.comp f)) := Matrix.map_map
  have hsp : p.f ((c * BK.hf f bk.E) ^ (S.a + S.b) * (BK.hf f bk.E ^ S.a * c ^ S.b)) =
      (p.f c * BK.hf (p.comp f) bk.E) ^ (S.a + S.b) * (BK.hf (p.comp f) bk.E ^ S.a * p.f c ^ S.b) := by
    simp only [map_mul, map_pow]; rfl
  have hsq : q.f ((c * BK.hf f bk.E) ^ (S.a + S.b) * (BK.hf f bk.E ^ S.a * c ^ S.b)) =
      (q.f c * BK.hf (q.comp f) bk.E) ^ (S.a + S.b) * (BK.hf (q.comp f) bk.E ^ S.a * q.f c ^ S.b) := by
    simp only [map_mul, map_pow]; rfl
  refine ((map_smul_mulVec p.f _ _ _).trans ?_).trans
    (congrArg (Matrix.mulVec ((S.ε (p.comp f) (q.comp f)).map D.D.φ)) (map_smul_mulVec q.f _ _ _)).symm
  exact (congrArg₂ (· • ·) hsp (congrArg₂ Matrix.mulVec hmp hv)).trans (key.trans
    (congrArg (Matrix.mulVec ((S.ε (p.comp f) (q.comp f)).map D.D.φ))
      (congrArg₂ (· • ·) hsq (congrArg₂ Matrix.mulVec hmq rfl))).symm)

theorem coord_relation {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ} {S : Strat bk d}
    {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N] (V : Eval S B N) {t : B.A}
    {Ψ : N →ₛₗ[B.D.φ] N} (hΨ : IsPsi V t Ψ) {P : Type} [AddCommGroup P] [Module B.A P] {u : N →ₛₗ[B.D.φ] P}
    (hu : SemiBC u) (L : P →ₗ[B.A] N) (hL : ∀ x, L (u x) = Ψ x) {C : Obj l ↥(OL K)} (h : Hom B C)
    (f : Hom bk.prism C) (hEnzd : BK.hf f bk.E ∈ nonZeroDivisors C.A) (κ : P →ₛₗ[h.f] (Fin d → C.A))
    (hκu : ∀ x i, κ (u x) i = C.D.φ (V.v h f x i)) (c : C.A) (hc : c * BK.hf f bk.E = h.f t) (y : P) :
    V.v h f (L y) = c ^ S.a • (S.A.map (BK.hf f)) *ᵥ (κ y) := by
  refine induction_bc hu (fun y => V.v h f (L y) = c ^ S.a • (S.A.map (BK.hf f)) *ᵥ (κ y))
    (fun x => ?_) (fun y z (hy : V.v h f (L y) = _) (hz : V.v h f (L z) = _) => ?_)
    (fun b y (hy : V.v h f (L y) = _) => ?_) y
  · show V.v h f (L (u x)) = c ^ S.a • (S.A.map (BK.hf f)) *ᵥ (κ (u x))
    have h2 : (fun i => C.D.φ (V.v h f x i)) = κ (u x) := funext fun i => (hκu x i).symm
    exact smul_cancel_nzd (pow_mem hEnzd S.a)
      ((congrArg (fun v => BK.hf f bk.E ^ S.a • V.v h f v) (hL x)).trans ((hΨ h f x).trans
        ((congrArg (fun v => h.f t ^ S.a • (S.A.map (BK.hf f)) *ᵥ v) h2).trans
          ((congrArg (fun s => s ^ S.a • (S.A.map (BK.hf f)) *ᵥ (κ (u x))) hc.symm).trans
            (mul_pow_smul _ _ _ _)))))
  · exact ((congrArg (V.v h f) (L.map_add y z)).trans ((V.v h f).map_add _ _)).trans
      ((congrArg₂ (· + ·) hy hz).trans
        ((congrArg (fun v => c ^ S.a • (S.A.map (BK.hf f)) *ᵥ v) (κ.map_add y z)).trans
          ((congrArg (c ^ S.a • ·) (Matrix.mulVec_add _ _ _)).trans (smul_add _ _ _))).symm)
  · exact ((congrArg (V.v h f) (L.map_smul b y)).trans ((V.v h f).map_smulₛₗ _ _)).trans
      ((congrArg (h.f b • ·) hy).trans
        ((congrArg (fun v => c ^ S.a • (S.A.map (BK.hf f)) *ᵥ v) (κ.map_smulₛₗ b y)).trans
          ((congrArg (c ^ S.a • ·) (Matrix.mulVec_smul _ _ _)).trans (smul_comm _ _ _))).symm)

set_option maxHeartbeats 400000 in

theorem linFrob_inv_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d)
    (B : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (V : Eval S B N) (t : B.A), t ∈ B.I →
    ∀ Ψ : N →ₛₗ[B.D.φ] N, IsPsi V t Ψ → ∀ (P : Type) [AddCommGroup P] [Module B.A P] (u : N →ₛₗ[B.D.φ] P),
    SemiBC u → ∀ L : P →ₗ[B.A] N, (∀ x, L (u x) = Ψ x) →
    ∃ n : ℕ, (∀ y, L y = 0 → t ^ n • y = 0) ∧ ∀ x, ∃ y, L y = t ^ n • x := by
  intro l _ K bk d S B N _ _ V t ht Ψ hΨ P _ _ u hu L hL
  haveI := V.fin
  haveI := V.proj
  obtain ⟨hPf, hPp⟩ := hu.finite_projective
  obtain ⟨C, h, ⟨f⟩, hC⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B
  obtain ⟨D, p, q, hpo⟩ := hC.stable.po C h
  obtain ⟨hinj, heq⟩ := GlobalTheory.T.prism_cover_injective_and_descent l ↥(OL K) B C h hC
  obtain ⟨hEC, hEnzd⟩ := GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk C f
  obtain ⟨hVinj, -⟩ := GlobalTheory.T.injective_and_range_of_prism_cover l K bk d S B C N V h f hC
  obtain ⟨κ, hκbc, hκu⟩ := exists_kappa V hu h f
  obtain ⟨κD, hκDbc, hκDu⟩ := exists_kappa V hu (p.comp h) (p.comp f)
  have htC : h.f t ∈ C.I := h.f_I t ht
  rw [hEC] at htC
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 htC
  have hAC := map_A_mul S (BK.hf f)
  have hA'C := mul_eq_smul_comm (pow_mem hEnzd S.b) hAC
  have hR := coord_relation V hΨ hu L hL h f hEnzd κ hκu c hc

  have hV2 : ∀ x, V.v (p.comp h) (q.comp f) x = V.v (q.comp h) (q.comp f) x := fun x =>
    congrArg (fun a : Hom B D => V.v a (q.comp f) x) hpo.comm
  have e1 : ∀ x, V.v (p.comp h) (p.comp f) x =
      (S.ε (p.comp f) (q.comp f)) *ᵥ (fun j => q.f (V.v h f x j)) := fun x =>
    (V.v_ε (p.comp h) (p.comp f) (q.comp f) x).trans (congrArg (Matrix.mulVec (S.ε (p.comp f) (q.comp f)))
      ((hV2 x).trans (funext fun j => V.v_nat q h f x j)))
  obtain ⟨u₁, hu₁⟩ : ∃ u₁ : (Fin d → C.A) →ₛₗ[p.f] (Fin d → D.A), ∀ z, u₁ z = fun i => p.f (z i) :=
    ⟨piMap p.f, piMap_apply p.f⟩
  obtain ⟨u₂, hu₂⟩ : ∃ u₂ : (Fin d → C.A) →ₛₗ[q.f] (Fin d → D.A),
      ∀ z, u₂ z = ((S.ε (p.comp f) (q.comp f)).map D.D.φ) *ᵥ (fun i => q.f (z i)) :=
    ⟨piMapMul q.f _, piMapMul_apply q.f _⟩
  have hw1 : ∀ y, κD y = u₁ (κ y) := by
    intro y
    refine induction_bc hu (fun y => κD y = u₁ (κ y)) (fun x => ?_)
      (fun y z (hy : κD y = _) (hz : κD z = _) => ?_) (fun b y (hy : κD y = _) => ?_) y
    · exact (funext fun i => (hκDu x i).trans ((congrArg D.D.φ (V.v_nat p h f x i)).trans
        ((p.f_φ _).symm.trans (congrArg p.f (hκu x i).symm)))).trans (hu₁ _).symm
    · exact (κD.map_add y z).trans ((congrArg₂ (· + ·) hy hz).trans
        ((congrArg u₁ (κ.map_add y z)).trans (u₁.map_add _ _)).symm)
    · exact (κD.map_smulₛₗ b y).trans ((congrArg ((p.comp h).f b • ·) hy).trans
        ((congrArg u₁ (κ.map_smulₛₗ b y)).trans (u₁.map_smulₛₗ _ _)).symm)
  have hw2 : ∀ y, κD y = u₂ (κ y) := by
    intro y
    refine induction_bc hu (fun y => κD y = u₂ (κ y)) (fun x => ?_)
      (fun y z (hy : κD y = _) (hz : κD z = _) => ?_) (fun b y (hy : κD y = _) => ?_) y
    · refine (funext fun i => ?_).trans (hu₂ _).symm
      exact (hκDu x i).trans ((congrArg (fun v => D.D.φ (v i)) (e1 x)).trans
        ((RingHom.map_mulVec D.D.φ _ _ i).trans
          (congrArg (fun v => (((S.ε (p.comp f) (q.comp f)).map D.D.φ) *ᵥ v) i)
            (funext fun j => (q.f_φ _).symm.trans (congrArg q.f (hκu x j).symm)))))
    · exact (κD.map_add y z).trans ((congrArg₂ (· + ·) hy hz).trans
        ((congrArg u₂ (κ.map_add y z)).trans (u₂.map_add _ _)).symm)
    · have hb : (p.comp h).f b = q.f (h.f b) := RingHom.congr_fun (congrArg Hom.f hpo.comm) b
      exact (κD.map_smulₛₗ b y).trans ((congrArg ((p.comp h).f b • ·) hy).trans
        ((congrArg (· • u₂ (κ y)) hb).trans ((congrArg u₂ (κ.map_smulₛₗ b y)).trans (u₂.map_smulₛₗ _ _)).symm))
  haveI := hPf
  haveI := hPp
  obtain ⟨hκinj, hdesc⟩ := GlobalTheory.T.finite_projective_module_element_descent_equalizer B.A C.A D.A h.f p.f q.f (congrArg Hom.f hpo.comm) hinj
    (fun b hb => heq D p q hpo b hb) P (Fin d → C.A) (Fin d → D.A) κ u₁ u₂ κD hκbc hκDbc hw1 hw2
  refine ⟨2 * (S.a + S.b), fun y hy => ?_, fun x => ?_⟩
  ·
    have h0 : t ^ (S.a + S.b) • y = 0 := hκinj (((κ.map_smulₛₗ _ _).trans
      ((congrArg (· • κ y) ((map_pow h.f t _).trans (congrArg (· ^ (S.a + S.b)) hc.symm))).trans
        (ker_gen hA'C ((hR y).symm.trans ((congrArg (V.v h f) hy).trans (map_zero _)))))).trans (map_zero κ).symm)
    exact smul_pow_two_mul h0
  ·
    have hcomp : u₁ ((h.f t ^ (S.a + S.b) * (BK.hf f bk.E ^ S.a * c ^ S.b)) •
        ((S.A'.map (BK.hf f)) *ᵥ (V.v h f x))) = u₂ ((h.f t ^ (S.a + S.b) * (BK.hf f bk.E ^ S.a * c ^ S.b)) •
        ((S.A'.map (BK.hf f)) *ᵥ (V.v h f x))) :=
      (hu₁ _).trans ((descent_compat S f p q c (h.f t) (RingHom.congr_fun (congrArg Hom.f hpo.comm) t) hc
        (V.v h f x) ((funext fun i => (V.v_nat p h f x i).symm).trans (e1 x))).trans (hu₂ _).symm)
    obtain ⟨y, hy⟩ := hdesc _ hcomp
    refine ⟨y, hVinj ?_⟩
    have e3 : c ^ S.a • (S.A.map (BK.hf f)) *ᵥ ((h.f t ^ (S.a + S.b) * (BK.hf f bk.E ^ S.a * c ^ S.b)) •
        ((S.A'.map (BK.hf f)) *ᵥ (V.v h f x))) = h.f t ^ (2 * (S.a + S.b)) • V.v h f x :=
      img_gen hAC hc.symm _
    exact (hR y).trans ((congrArg (fun v => c ^ S.a • (S.A.map (BK.hf f)) *ᵥ v) hy).trans
      (e3.trans (((V.v h f).map_smulₛₗ _ _).trans (congrArg (· • V.v h f x) (map_pow h.f t _))).symm))
end GlobalTheory.BSP.LinFrob
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearizedFrobenius_invertible_up_to_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (V : Eval S B N) (t : B.A), t ∈ B.I → ∀ Ψ : N →ₛₗ[B.D.φ] N, IsPsi V t Ψ → ∀ (P : Type) [AddCommGroup P] [Module B.A P] (u : N →ₛₗ[B.D.φ] P), SemiBC u → ∀ L : P →ₗ[B.A] N, (∀ x, L (u x) = Ψ x) → ∃ n : ℕ, (∀ y, L y = 0 → t ^ n • y = 0) ∧ ∀ x, ∃ y, L y = t ^ n • x := by
  atlas_forward_decl GlobalTheory.BSP.LinFrob.linFrob_inv_pow
end

section
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.StratCrys

theorem exists_semiBC {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (M : Type) [AddCommGroup M]
    [Module A M] : ∃ (P : Type) (_ : AddCommGroup P) (_ : Module B P) (u : M →ₛₗ[f] P), SemiBC u := by
  letI := f.toAlgebra
  let u : M →ₛₗ[algebraMap A B] (B ⊗[A] M) :=
    { toFun := fun x => 1 ⊗ₜ x
      map_add' := fun x y => TensorProduct.tmul_add _ _ _
      map_smul' := fun a x => by rw [algebraMap_smul, TensorProduct.tmul_smul] }
  exact ⟨B ⊗[A] M, inferInstance, inferInstance, u,
    (GlobalTheory.T.isSemilinearBaseChange_iff_isBaseChange A B M (B ⊗[A] M) u (TensorProduct.mk A B M 1) fun _ => rfl).2
      (TensorProduct.isBaseChange A M B)⟩

theorem bijective_of_semiBC {A M N : Type} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (u : M →ₗ[A] N) (h : SemiBC u) : Function.Bijective u := by
  obtain ⟨w, hw, -⟩ := h M LinearMap.id
  have h2 : u.comp w = LinearMap.id := h.hom_ext fun x => congrArg u (hw x)
  exact ⟨Function.LeftInverse.injective (g := w) hw, fun y => ⟨w y, LinearMap.congr_fun h2 y⟩⟩

def fracMap {A N : Type} [CommRing A] [AddCommGroup N] [Module A N] {φ : A →+* A} (t : A) (a : ℕ)
    (Ψ : N →ₛₗ[φ] N) :
    N →ₛₗ[(algebraMap A (Localization.Away t)).comp φ] LocalizedModule (Submonoid.powers t) N where
  toFun x := LocalizedModule.mk (Ψ x) ⟨t ^ a, (Submonoid.mem_powers_iff _ _).2 ⟨a, rfl⟩⟩
  map_add' x y := by
    rw [map_add, LocalizedModule.mk_add_mk, ← smul_add, LocalizedModule.mk_cancel_common_left]
  map_smul' c x := by
    rw [Ψ.map_smulₛₗ, RingHom.comp_apply, algebraMap_smul, LocalizedModule.smul'_mk]

theorem isFrac_fracMap {A N : Type} [CommRing A] [AddCommGroup N] [Module A N] {φ : A →+* A} (t : A) (a : ℕ)
    (Ψ : N →ₛₗ[φ] N) (x : N) : IsFrac t (fracMap t a Ψ x) (Ψ x) a := rfl

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ} {S : Strat bk d}

theorem eval_ext {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N] (V : Eval S B N) {x y : N}
    (h : ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q), V.v a g x = V.v a g y) : x = y := by
  obtain ⟨C, c, ⟨f⟩, hc⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B
  exact (GlobalTheory.T.injective_and_range_of_prism_cover l K bk d S B C N V c f hc).1 (h C c f)

theorem v_id_bijective {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N] (V : Eval S B N)
    (f : Hom bk.prism B) : Function.Bijective (V.v (Hom.id B) f) :=
  bijective_of_semiBC (A := B.A) (V.v (Hom.id B) f) (V.bc (Hom.id B) f)

theorem semiBC_fracMap {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N] (V : Eval S B N)
    (t : B.A) (ht : t ∈ B.I) (Ψ : N →ₛₗ[B.D.φ] N) (hΨ : IsPsi V t Ψ) : SemiBC (fracMap t S.a Ψ) := by
  obtain ⟨P, _, _, u, hu⟩ := exists_semiBC B.D.φ N
  obtain ⟨L, hL, -⟩ := hu N Ψ
  obtain ⟨n, h1, h2⟩ := GlobalTheory.T.linearizedFrobenius_invertible_up_to_pow l K bk d S B N V t ht Ψ hΨ P u hu L hL
  exact GlobalTheory.T.isSemilinearBaseChange_localized_of_torsion_bounded B.A B.D.φ t N P u hu L n S.a h1 h2 _ fun x => by
    rw [hL]; exact isFrac_fracMap _ _ _ _

variable (S) in

theorem exists_crys : ∃ (M : FCrys l ↥(OL K)) (V : ∀ B, Eval S B (M.M B)),
    (∀ (B B' Q : Obj l ↥(OL K)) (k : Hom B B') (a : Hom B' Q) (g : Hom bk.prism Q) (x : M.M B),
      (V B').v a g (M.tr k x) = (V B).v (a.comp k) g x) ∧
    ∀ (B : Obj l ↥(OL K)) (t : ↥B.I), ∃ Ψ : M.M B →ₛₗ[B.D.φ] M.M B, IsPsi (V B) t Ψ ∧
      ∀ x, IsFrac (t : B.A) (M.Φ B t x) (Ψ x) S.a := by
  choose N acg mod hV using GlobalTheory.T.exists_stratifiedPhiModuleValue l K bk d S
  have V : ∀ B, Eval S B (N B) := fun B => (hV B).some
  choose tr trbc htr using fun (B B' : Obj l ↥(OL K)) (k : Hom B B') =>
    GlobalTheory.T.exists_stratifiedValue_transition_baseChange l K bk d S B B' (N B) (N B') (V B) (V B') k
  choose Ψ hΨ using fun (B : Obj l ↥(OL K)) (t : ↥B.I) =>
    GlobalTheory.T.exists_frobenius_on_stratifiedValue l K bk d S B (N B) (V B) t t.2
  let M : FCrys l ↥(OL K) :=
    { M := N
      acg := acg
      mod := mod
      fin := fun B => (V B).fin
      proj := fun B => (V B).proj
      tr := fun k => tr _ _ k
      tr_bc := fun k => trbc _ _ k
      tr_id := fun B x => eval_ext (V B) fun Q a g => htr _ _ _ Q a g x
      tr_comp := fun {B B' B''} k' k x => eval_ext (V B'') fun Q a g =>
        (htr _ _ (k'.comp k) Q a g x).trans
          ((htr _ _ k' Q a g _).trans (htr _ _ k Q (a.comp k') g x)).symm
      Φ := fun B t => fracMap (t : B.A) S.a (Ψ B t)
      Φ_bc := fun B t => semiBC_fracMap (V B) t t.2 _ (hΨ B t)
      Φ_nat := fun {B B'} k t t' x m i n j h1 h2 =>
        GlobalTheory.T.isLocalizedFraction_semilinear_transition B.A B'.A k.f (N B) (N B') (tr _ _ k) t t' S.a _ _ _ m _ n i j
          (isFrac_fracMap _ _ _ _) h1 (isFrac_fracMap _ _ _ _) h2
          (GlobalTheory.T.stratifiedValue_frobenius_comm_transition l K bk d S B B' (N B) (N B') (V B) (V B') k (tr _ _ k) (htr _ _ k) t t' _ _
            (hΨ B t) (hΨ B' t') x) }
  exact ⟨M, V, fun B B' Q k a g x => htr _ _ k Q a g x, fun B t => ⟨Ψ B t, hΨ B t, fun _ => rfl⟩⟩

theorem map_single {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (j i : Fin d) :
    f ((Pi.single j 1 : Fin d → A) i) = (Pi.single j 1 : Fin d → B) i := by
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem sum_single {A : Type} [CommRing A] (c : Fin d → A) :
    ∑ i, c i • (Pi.single i 1 : Fin d → A) = c := by
  ext i
  simp [Finset.sum_apply, Pi.single_apply]

theorem exists_basis {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N] (V : Eval S B N)
    (f : Hom bk.prism B) : ∃ e : Module.Basis (Fin d) B.A N, ∀ j, V.v (Hom.id B) f (e j) = Pi.single j 1 := by
  let w : N →ₗ[B.A] (Fin d → B.A) := V.v (Hom.id B) f
  let q : N ≃ₗ[B.A] (Fin d → B.A) := LinearEquiv.ofBijective w (v_id_bijective V f)
  refine ⟨(Pi.basisFun _ _).map q.symm, fun j => ?_⟩
  change q _ = _
  simp

theorem eq_sum_of_coord {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N] (V : Eval S B N)
    (f : Hom bk.prism B) (e : Fin d → N) (he : ∀ j, V.v (Hom.id B) f (e j) = Pi.single j 1) (x : N)
    (c : Fin d → B.A) (h : V.v (Hom.id B) f x = c) : x = ∑ i, c i • e i := by
  apply (v_id_bijective V f).1
  let w : N →ₗ[B.A] (Fin d → B.A) := V.v (Hom.id B) f
  have he' : ∀ j, w (e j) = Pi.single j 1 := he
  change _ = w _
  rw [h, map_sum]
  simp only [map_smul, he']
  exact (sum_single c).symm

theorem coord_psi {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N] (V : Eval S B N)
    (f : Hom bk.prism B) (t : B.A) (ht : t = BK.hf f bk.E) (Ψ : N →ₛₗ[B.D.φ] N) (hΨ : IsPsi V t Ψ) (x : N)
    (j : Fin d) (hx : V.v (Hom.id B) f x = Pi.single j 1) :
    V.v (Hom.id B) f (Ψ x) = fun i => BK.hf f (S.A i j) := by
  have h1 := hΨ (Hom.id B) f x
  rw [hx, funext (map_single B.D.φ j), Matrix.mulVec_single_one] at h1
  subst ht
  ext i
  exact (mul_cancel_left_mem_nonZeroDivisors (pow_mem (GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk B f).2 S.a)).1 (congrFun h1 i)

theorem exists_framed (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) :
    ∃ (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e := by
  obtain ⟨M, V, htr, hΦ⟩ := exists_crys S
  obtain ⟨e, he⟩ := exists_basis (V bk.prism) (Hom.id _)
  have he' : ∀ {B : Obj l ↥(OL K)} (g : Hom bk.prism B) j, (V bk.prism).v g g (e j) = Pi.single j 1 :=
    fun g j => by
      ext i
      have := (V bk.prism).v_nat g (Hom.id _) (Hom.id _) (e j) i
      rw [he, map_single] at this
      exact this
  refine ⟨M, e, ⟨fun {B} f g j => ?_, fun j => ?_⟩⟩
  · have h1 : ∀ (g : Hom bk.prism B) x, (V B).v (Hom.id B) f (M.tr g x) = (V bk.prism).v g f x :=
      fun g x => htr _ _ B g (Hom.id B) f x
    refine eq_sum_of_coord (V B) f (fun i => M.tr f (e i)) (fun i => (h1 f _).trans (he' f i)) _
      (fun i => S.ε f g i j) ?_
    rw [h1, (V _).v_ε g f g, he', Matrix.mulVec_single_one]
    rfl
  · have h0 : ∀ x, BK.hf (Hom.id bk.prism) x = bk.toP x := fun _ => rfl
    have ht : bk.toP bk.E ∈ bk.prism.I := by
      rw [(GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk bk.prism (Hom.id _)).1, h0]
      exact Ideal.mem_span_singleton_self _
    have hh := hΦ bk.prism ⟨bk.toP bk.E, ht⟩
    obtain ⟨Ψ, hΨ, h⟩ := hh
    have h1 := coord_psi (V _) (Hom.id _) _ (h0 _).symm Ψ hΨ _ j (he j)
    have h2 := eq_sum_of_coord (V _) (Hom.id _) e he _ _ h1
    simp only [h0] at h2
    exact Eq.mp (congrArg (fun m => IsFrac (bk.toP bk.E) (M.Φ bk.prism ⟨bk.toP bk.E, ht⟩ (e j)) m S.a) h2)
      (h (e j))

end GlobalTheory.BSP.StratCrys
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_framed_fCrystal_of_stratifiedPhiModule : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d), ∃ (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e := by
  atlas_forward_decl GlobalTheory.BSP.StratCrys.exists_framed
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem semiBC_of_basis : ∀ (A B : Type) [CommRing A] [CommRing B] (f : A →+* B) (M : Type) [AddCommGroup M] [Module A M] (N : Type) [AddCommGroup N] [Module B N] (u : M →ₛₗ[f] N) (ι : Type) (e : Module.Basis ι A M) (b : Module.Basis ι B N), (∀ i, b i = u (e i)) → SemiBC u := by
  intro A B _ _ f M _ _ N _ _ u ι e b hb Q _ _ v
  refine ⟨b.constr B (fun i => v (e i)), ?_, ?_⟩
  · intro x
    have h : (b.constr B (fun i => v (e i))).comp u = v := by
      refine e.ext fun i => ?_
      simp [LinearMap.comp_apply, ← hb, Module.Basis.constr_basis]
    exact LinearMap.congr_fun h x
  · intro w hw
    refine b.ext fun i => ?_
    rw [Module.Basis.constr_basis, hb, hw]

end GlobalTheory.BSP
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSemilinearBaseChange_of_basis_maps_to_basis : ∀ (A B : Type) [CommRing A] [CommRing B] (f : A →+* B) (M : Type) [AddCommGroup M] [Module A M] (N : Type) [AddCommGroup N] [Module B N] (u : M →ₛₗ[f] N) (ι : Type) (e : Module.Basis ι A M) (b : Module.Basis ι B N), (∀ i, b i = u (e i)) → SemiBC u := by
  atlas_forward_decl GlobalTheory.BSP.semiBC_of_basis
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.EtReal

open Matrix

variable {l : ℕ} [hl : Fact l.Prime]

theorem equivFun_frob {T : Type} [AddCommGroup T] [Module ℤ_[l] T] {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ_[l] T) (y : WCb l ⊗[ℤ_[l]] T) :
    (b.baseChange (WCb l)).equivFun (TensorProduct.map (frobW l).toLinearMap LinearMap.id y) =
      fun i => frobW l ((b.baseChange (WCb l)).equivFun y i) := by
  funext i
  simp only [Module.Basis.equivFun_apply]
  induction y with
  | zero => rw [map_zero, map_zero, Finsupp.zero_apply, map_zero]
  | tmul a t =>
    rw [TensorProduct.map_tmul, Module.Basis.baseChange_repr_tmul, Module.Basis.baseChange_repr_tmul,
      map_smul, AlgHom.toLinearMap_apply, LinearMap.id_apply]
  | add y z hy hz => rw [map_add, map_add, map_add, Finsupp.add_apply, Finsupp.add_apply, map_add, hy, hz]

theorem equivFun_map {T : Type} [AddCommGroup T] [Module ℤ_[l] T] {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ_[l] T) (s : WCb l ≃ₐ[ℤ_[l]] WCb l) (r : T →ₗ[ℤ_[l]] T) (y : WCb l ⊗[ℤ_[l]] T) :
    (b.baseChange (WCb l)).equivFun (TensorProduct.map s.toLinearMap r y) =
      (LinearMap.toMatrix b b r).map (algebraMap ℤ_[l] (WCb l)) *ᵥ
        fun k => s ((b.baseChange (WCb l)).equivFun y k) := by
  funext i
  simp only [Module.Basis.equivFun_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  induction y with
  | zero => simp
  | tmul a t =>
    rw [TensorProduct.map_tmul, Module.Basis.baseChange_repr_tmul, AlgEquiv.toLinearMap_apply,
      ← LinearMap.toMatrix_mulVec_repr b b r t]
    simp only [Module.Basis.baseChange_repr_tmul, Matrix.mulVec, dotProduct, map_smul, Algebra.smul_def,
      Finset.sum_mul, map_mul, mul_assoc, map_sum, AlgEquiv.commutes]
  | add y z hy hz =>
    simp only [map_add, Finsupp.add_apply, hy, hz, mul_add, Finset.sum_add_distrib]

theorem algEquiv_mulVec {R A : Type} [CommSemiring R] [CommRing A] [Algebra R A] {n : Type} [Fintype n]
    (s : A ≃ₐ[R] A) (U : Matrix n n A) (v : n → A) (i : n) :
    s ((U *ᵥ v) i) = (U.map s *ᵥ fun k => s (v k)) i :=
  RingHom.map_mulVec s.toRingEquiv.toRingHom U v i

theorem realises_of_mreal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e → ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (b : Module.Basis (Fin d) ℤ_[l] T) (U : Matrix (Fin d) (Fin d) (WCb l)), MReal S (fun g => LinearMap.toMatrix b b (ρ g)) U → ∃ j : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M (ainfObj K) (ainfId K) T ρ j := by
  intro l _ K bk d S M e hF T _ _ ρ b U hU
  obtain ⟨b₀, hb₀⟩ := GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ _ _ _ (M.tr bk.ι) (M.tr_bc bk.ι) _ e
  let σ : (ainfObj K).A →+* WCb l := (inclW l).comp (ainfId K).toRingHom
  let cv : (Fin d → (ainfObj K).A) →ₛₗ[σ] (Fin d → WCb l) :=
    { toFun := fun v k => σ (v k)
      map_add' := fun v w => funext fun k => map_add σ (v k) (w k)
      map_smul' := fun a v => funext fun k => map_mul σ a (v k) }
  let j : M.M (ainfObj K) →ₛₗ[σ] (WCb l ⊗[ℤ_[l]] T) :=
    ((b.baseChange (WCb l)).equivFun.symm.toLinearMap ∘ₗ Matrix.toLin' U) ∘ₛₗ (cv ∘ₛₗ b₀.equivFun.toLinearMap)
  have hj : ∀ x, (b.baseChange (WCb l)).equivFun (j x) = U *ᵥ fun k => σ (b₀.equivFun x k) := fun x =>
    (b.baseChange (WCb l)).equivFun.apply_symm_apply _
  have hjs : ∀ c : Fin d → (ainfObj K).A, (b.baseChange (WCb l)).equivFun (j (b₀.equivFun.symm c)) = U *ᵥ fun k => σ (c k) := fun c => by
    rw [hj, LinearEquiv.apply_symm_apply]

  have hbc : SemiBC j := by
    letI := hU.unit.invertible
    let c := (Pi.basisFun (WCb l) (Fin d)).map ((Matrix.toLinearEquiv' U this).trans (b.baseChange (WCb l)).equivFun.symm)
    refine GlobalTheory.T.isSemilinearBaseChange_of_basis_maps_to_basis _ _ _ _ _ j (Fin d) b₀ c fun i => ?_
    apply (b.baseChange (WCb l)).equivFun.injective
    rw [hj]
    simp only [c, Module.Basis.map_apply, Pi.basisFun_apply, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply, Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply]
    refine congrArg _ (funext fun k => ?_)
    rw [Module.Basis.equivFun_self]
    by_cases h : i = k
    · subst h; simp
    · simp [h, Pi.single_apply, Ne.symm h]
  have hu : IsUnit (inclW l (bk.ev bk.E)) := isUnit_inclW_of_span bk.span_ev
  obtain ⟨d₀, hd₀⟩ : ∃ d₀ : ↥(ainfObj K).I, ((d₀ : (ainfObj K).A) : Ainf l) = bk.ev bk.E :=
    ⟨⟨bk.ι.f bk.E, bk.ι.f_I _ (Ideal.mem_span_singleton_self _)⟩, rfl⟩
  have hne : (d₀ : (ainfObj K).A) ≠ 0 := fun h => hu.ne_zero (by rw [← hd₀, h]; exact map_zero (inclW l))
  refine ⟨j, Realises.of_generator (isAinf_ainfObj K) hbc d₀ (by rw [hd₀]; exact bk.span_ev) ?_ ?_⟩
  · intro x m k hfr
    have hx : x = ∑ i, b₀.equivFun x i • M.tr bk.ι (e i) := by
      simp_rw [← hb₀]; exact (b₀.sum_equivFun x).symm
    rw [hx] at hfr
    obtain ⟨r, hr⟩ := GlobalTheory.T.prismaticFCrystal_frobenius_pullback_basis l K bk d M e S.a S.A hF.Φ (ainfObj K) bk.ι d₀ (b₀.equivFun x) m k hfr
    haveI : IsDomain (ainfObj K).A := (ainfId K).toMulEquiv.isDomain
    haveI := Module.Free.of_basis b₀
    have h1 := sub_eq_zero.1 ((smul_eq_zero.1 hr).resolve_left (pow_ne_zero _ hne))
    simp_rw [← hb₀] at h1
    rw [← b₀.equivFun_symm_apply] at h1
    have h2 : σ (BK.hf bk.ι bk.E) ^ S.a • j m = σ (d₀ : (ainfObj K).A) ^ k •
        j (b₀.equivFun.symm ((S.A.map (BK.hf bk.ι)) *ᵥ fun i => (ainfObj K).D.φ (b₀.equivFun x i))) :=
      calc σ (BK.hf bk.ι bk.E) ^ S.a • j m = σ (BK.hf bk.ι bk.E ^ S.a) • j m := by rw [map_pow]
        _ = j (BK.hf bk.ι bk.E ^ S.a • m) := (j.map_smulₛₗ _ _).symm
        _ = j ((d₀ : (ainfObj K).A) ^ k • b₀.equivFun.symm ((S.A.map (BK.hf bk.ι)) *ᵥ
              fun i => (ainfObj K).D.φ (b₀.equivFun x i))) := congrArg j h1
        _ = σ ((d₀ : (ainfObj K).A) ^ k) • j (b₀.equivFun.symm ((S.A.map (BK.hf bk.ι)) *ᵥ
              fun i => (ainfObj K).D.φ (b₀.equivFun x i))) := j.map_smulₛₗ _ _
        _ = _ := congrArg (· • _) (map_pow σ _ _)
    suffices hs : σ (BK.hf bk.ι bk.E) ^ S.a • (σ (d₀ : (ainfObj K).A) ^ k •
        TensorProduct.map (frobW l).toLinearMap LinearMap.id (j x)) = σ (BK.hf bk.ι bk.E) ^ S.a • j m from
      (hu.pow S.a).smul_left_cancel.1 hs
    rw [h2]
    refine (smul_comm (σ (BK.hf bk.ι bk.E) ^ S.a) (σ (d₀ : (ainfObj K).A) ^ k) _).trans
      (congrArg (σ (d₀ : (ainfObj K).A) ^ k • ·) ?_)
    apply (b.baseChange (WCb l)).equivFun.injective
    have hz : (fun i => frobW l ((b.baseChange (WCb l)).equivFun (j x) i)) =
        U.map (frobW l) *ᵥ fun k => σ ((ainfObj K).D.φ (b₀.equivFun x k)) := by
      rw [hj]
      funext i
      refine (RingHom.map_mulVec (frobW l).toRingHom U _ i).trans ?_
      exact congrArg (fun v => (U.map (frobW l) *ᵥ v) i) (funext fun k => frobW_inclW (b₀.equivFun x k))
    have hc : (fun k => σ (((S.A.map (BK.hf bk.ι)) *ᵥ fun i => (ainfObj K).D.φ (b₀.equivFun x i)) k)) =
        S.A.map bk.evW *ᵥ fun k => σ ((ainfObj K).D.φ (b₀.equivFun x k)) := by
      funext k
      have hA : (S.A.map (BK.hf bk.ι)).map σ = S.A.map bk.evW := Matrix.ext fun _ _ => rfl
      exact (RingHom.map_mulVec σ _ _ k).trans
        (congrArg (fun A => (A *ᵥ fun k => σ ((ainfObj K).D.φ (b₀.equivFun x k))) k) hA)
    have hσE : σ (BK.hf bk.ι bk.E) = bk.evW bk.E := rfl
    refine ((b.baseChange (WCb l)).equivFun.map_smul _ _).trans ?_
    refine Eq.trans ?_ (hjs _).symm
    refine (congrArg (σ (BK.hf bk.ι bk.E) ^ S.a • ·) ((equivFun_frob b (j x)).trans hz)).trans ?_
    refine Eq.trans ?_ (congrArg (U *ᵥ ·) hc).symm
    exact (congrArg (fun t => t ^ S.a • (U.map (frobW l) *ᵥ _)) hσE).trans
      ((Matrix.smul_mulVec _ _ _).symm.trans
        ((congrArg (· *ᵥ _) hU.φ).trans (Matrix.mulVec_mulVec _ _ _).symm))
  · intro g x
    let h := (isAinf_ainfObj K).galHom g
    have hk : ∀ k, M.tr h (b₀ k) = ∑ i, S.ε bk.ι (h.comp bk.ι) i k • b₀ i := fun k =>
      (congrArg (M.tr h) (hb₀ k)).trans ((M.tr_comp h bk.ι (e k)).symm.trans
        ((hF.tr bk.ι (h.comp bk.ι) k).trans (Finset.sum_congr rfl fun i _ => congrArg _ (hb₀ i).symm)))
    have htr : M.tr h x = b₀.equivFun.symm ((S.ε bk.ι (h.comp bk.ι)) *ᵥ fun k => h.f (b₀.equivFun x k)) :=
      calc M.tr h x = M.tr h (∑ k, b₀.equivFun x k • b₀ k) := congrArg (M.tr h) (b₀.sum_equivFun x).symm
        _ = ∑ k, h.f (b₀.equivFun x k) • M.tr h (b₀ k) :=
          (map_sum (M.tr h) _ _).trans (Finset.sum_congr rfl fun k _ => (M.tr h).map_smulₛₗ _ _)
        _ = ∑ k, ∑ i, (h.f (b₀.equivFun x k) * S.ε bk.ι (h.comp bk.ι) i k) • b₀ i :=
          Finset.sum_congr rfl fun k _ => (congrArg _ (hk k)).trans
            (Finset.smul_sum.trans (Finset.sum_congr rfl fun i _ => smul_smul _ _ _))
        _ = ∑ i, (∑ k, S.ε bk.ι (h.comp bk.ι) i k * h.f (b₀.equivFun x k)) • b₀ i :=
          Finset.sum_comm.trans (Finset.sum_congr rfl fun i _ =>
            (Finset.sum_congr rfl fun k _ => congrArg (· • b₀ i) (mul_comm _ _)).trans Finset.sum_smul.symm)
        _ = _ := (b₀.equivFun_symm_apply _).symm
    apply (b.baseChange (WCb l)).equivFun.injective
    have hσ : ∀ a : (ainfObj K).A, σ a = inclW l a := fun a => rfl
    have hh : ∀ a : (ainfObj K).A, h.f a = Per.σA (g : GQ l) a := fun a => rfl
    have hL : (fun k => σ (((S.ε bk.ι (h.comp bk.ι)) *ᵥ fun k => h.f (b₀.equivFun x k)) k)) =
        (S.ε bk.ι (h.comp bk.ι)).map σ *ᵥ fun k => σ (h.f (b₀.equivFun x k)) :=
      funext fun k => RingHom.map_mulVec σ _ _ k
    have hR : (fun k => galW l (g : GQ l) ((b.baseChange (WCb l)).equivFun (j x) k)) =
        U.map (galW l (g : GQ l)) *ᵥ fun k => σ (h.f (b₀.equivFun x k)) :=
      funext fun i => by
        have h1 := congrArg (fun v : Fin d → WCb l => galW l (g : GQ l) (v i)) (hj x)
        have h2 := algEquiv_mulVec (galW l (g : GQ l)) U (fun k => σ (b₀.equivFun x k)) i
        have h3 : (fun k => galW l (g : GQ l) (σ (b₀.equivFun x k))) = fun k => σ (h.f (b₀.equivFun x k)) :=
          funext fun k => (congrArg (galW l (g : GQ l)) (hσ _)).trans ((galW_inclW (g : GQ l) (b₀.equivFun x k)).trans
            ((hσ _).symm.trans (congrArg σ (hh _).symm)))
        beta_reduce at h1 ⊢
        exact h1.trans (h2.trans (congrArg (fun v => (U.map (galW l (g : GQ l)) *ᵥ v) i) h3))
    have hg := hU.gal g
    refine ((congrArg (fun z => (b.baseChange (WCb l)).equivFun (j z)) htr).trans (hjs _)).trans ?_
    refine Eq.trans ?_ (equivFun_map b _ _ _).symm
    refine (congrArg (U *ᵥ ·) hL).trans (Eq.trans ?_ (congrArg (_ *ᵥ ·) hR).symm)
    exact (Matrix.mulVec_mulVec _ _ _).trans ((congrArg (· *ᵥ _) hg.symm).trans (Matrix.mulVec_mulVec _ _ _).symm)

end GlobalTheory.BSP.EtReal
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleRealisation_of_framedMatrices : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e → ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (b : Module.Basis (Fin d) ℤ_[l] T) (U : Matrix (Fin d) (Fin d) (WCb l)), MReal S (fun g => LinearMap.toMatrix b b (ρ g)) U → ∃ j : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M (ainfObj K) (ainfId K) T ρ j := by
  atlas_forward_decl GlobalTheory.BSP.EtReal.realises_of_mreal
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem galoisLatticeAction_mul {l : ℕ} [Fact l.Prime] {K : FinExt l} {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] {ρ : Representation ℚ_[l] ↥(GK K) V}
    (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := ℤ_[l]) ρ) (g h : ↥(GK K)) :
    actT L g ∘ₗ actT L h = actT L (g * h) := by
  ext x
  simp [actT, map_mul]
  rfl

theorem galoisLatticeAction_one {l : ℕ} [Fact l.Prime] {K : FinExt l} {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] {ρ : Representation ℚ_[l] ↥(GK K) V}
    (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := ℤ_[l]) ρ) :
    actT L 1 = LinearMap.id := by
  ext x
  simp [actT, map_one]

end GlobalTheory.BSP

namespace GlobalTheory.BSP

theorem isUnit_toMatrix_actT {l : ℕ} [Fact l.Prime] {K : FinExt l} {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] {ρ : Representation ℚ_[l] ↥(GK K) V}
    (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := ℤ_[l]) ρ) {d : ℕ} (b : Module.Basis (Fin d) ℤ_[l] ↥L.T) (g : ↥(GK K)) :
    IsUnit (LinearMap.toMatrix b b (actT L g)) := by
  have h1 : LinearMap.toMatrix b b (actT L g) * LinearMap.toMatrix b b (actT L g⁻¹) = 1 := by
    rw [← LinearMap.toMatrix_comp, galoisLatticeAction_mul, mul_inv_cancel, galoisLatticeAction_one, LinearMap.toMatrix_id]
  have h2 : LinearMap.toMatrix b b (actT L g⁻¹) * LinearMap.toMatrix b b (actT L g) = 1 := by
    rw [← LinearMap.toMatrix_comp, galoisLatticeAction_mul, inv_mul_cancel, galoisLatticeAction_one, LinearMap.toMatrix_id]
  exact ⟨⟨_, _, h1, h2⟩, rfl⟩

theorem clause1_perfectPrism : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P), IsStd P AI → ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (L : Lattice (O := ℤ_[l]) ρ), (∀ x, Continuous fun g => ρ g x) → IsCrys (P.PD K) ρ → ∃ (M : FCrys l ↥(OL K)) (j : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] ↥L.T)), Realises K M (ainfObj K) (ainfId K) ↥L.T (fun g => actT L g) j := by
  intro l _ K P AI hStd V _ _ _ _ _ _ _ ρ L hcont hcrys
  haveI : Module.Free ℤ_[l] ↥L.T := L.free
  haveI : Module.Finite ℤ_[l] ↥L.T := Module.Finite.iff_fg.mpr L.fg
  obtain ⟨bk⟩ := GlobalTheory.T.nonempty_breuilKisinDatum l K
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_breuilKisin_frobenius_period l K bk
  let b := Module.finBasis ℤ_[l] ↥L.T
  obtain ⟨s⟩ := GlobalTheory.T.exists_crystalline_lattice_periods_on_disc l K bk τ hτ P AI hStd V ρ L hcont hcrys _ b
  have hu : ∀ g, IsUnit (LinearMap.toMatrix b b (actT L g)) := fun g => isUnit_toMatrix_actT L b g
  obtain ⟨hs⟩ := GlobalTheory.T.nonempty_discPeriodAinfBasisData_of_isPer l K bk τ hτ _ _ hu s
  obtain ⟨S, T, hST⟩ := GlobalTheory.T.exists_stratified_phiModule_crystalline_lattice l K bk τ hτ _ _ hu s hs
  obtain ⟨M, e, hMe⟩ := GlobalTheory.T.exists_framed_fCrystal_of_stratifiedPhiModule l K bk _ S
  exact ⟨M, GlobalTheory.T.etaleRealisation_of_framedMatrices l K bk _ S M e hMe ↥L.T (fun g => actT L g) b T hST⟩

end GlobalTheory.BSP
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineLattice_prismaticFCrystal_perfectPrism : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P), IsStd P AI → ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (L : Lattice (O := ℤ_[l]) ρ), (∀ x, Continuous fun g => ρ g x) → IsCrys (P.PD K) ρ → ∃ (M : FCrys l ↥(OL K)) (j : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] ↥L.T)), Realises K M (ainfObj K) (ainfId K) ↥L.T (fun g => actT L g) j := by
  atlas_forward_decl GlobalTheory.BSP.clause1_perfectPrism
end
