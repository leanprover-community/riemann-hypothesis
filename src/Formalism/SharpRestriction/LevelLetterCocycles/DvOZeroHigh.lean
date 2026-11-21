import Formalism.SharpRestriction.LevelLetterCocycles.CoprimeFrobeniusUniformizerPowers
import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd

section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup

theorem lam_unit (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (A : ArcP n) (a : ZMod n) (e : ℕ) :
    IsUnit (algebraMap (LetA O n) W.EE (abelian₂ W A a e)) := by
  obtain ⟨h3, h6⟩ := Formalism.MainNotions.UnusedSlot80.SatW.ring_clauses W hR
  exact Formalism.MainNotions.UnusedSlot80.SatW.isUnit_EE_of_UPi W
    (Formalism.MainNotions.UnusedSlot80.SatW.UPi.prod _ _ fun s _ => (Formalism.MainNotions.UnusedSlot80.SatW.UPi_qpow W h3 h6 s).pow _)

theorem lam_piPs (A : ArcP n) (a : ZMod n) (e : ℕ) : abelian₂ W A a e ∈ PiPs W :=
  Submonoid.prod_mem _ fun s _ => Submonoid.pow_mem _ (Submonoid.subset_closure
    (show ps W s ∈ insert W.π₀ (Set.range (ps W)) from Set.mem_insert_of_mem _ ⟨s, rfl⟩)) _

theorem piLam_piPs (A : ArcP n) (a : ZMod n) (e : ℕ) : W.π₀ * abelian₂ W A a e ∈ PiPs W :=
  Submonoid.mul_mem _ (Submonoid.subset_closure (Set.mem_insert _ _)) (lam_piPs W A a e)

theorem lA_smul_eq (T : LocLat G Qp LL O) (t : ℕ) (z : W.DD T) :
    lA W ^ t • z = (((PD.p : ℕ) : O) ^ t) • z := by
  rw [← algebraMap_smul (LetA O n) (((PD.p : ℕ) : O) ^ t) z, map_pow, map_natCast]
  rfl

theorem lA_smul_smul (T : LocLat G Qp LL O) (t s : ℕ) (z : W.DD T) :
    lA W ^ t • lA W ^ s • z = lA W ^ (s + t) • z := by
  rw [smul_smul, ← pow_add, add_comm]

theorem φpow_lA (T : LocLat G Qp LL O) (e t : ℕ) (z : W.DD T) :
    ((W.φD T) ^ e) (lA W ^ t • z) = lA W ^ t • ((W.φD T) ^ e) z := by
  rw [Formalism.MainNotions.UnusedSlot80.Relay2.φpow_smul, map_pow]
  congr 2
  unfold lA
  rw [map_natCast]

theorem vecB_smul (T : LocLat G Qp LL O) {d : ℕ} (b : Fin d → W.DD T) (c : O) (y : Fin d → O) :
    Formalism.MainNotions.LiftingTheory.vecB W T b (fun m => c * y m) = c • Formalism.MainNotions.LiftingTheory.vecB W T b y := by
  unfold Formalism.MainNotions.LiftingTheory.vecB
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun m _ => mul_smul _ _ _

theorem horTr_scale (T : LocLat G Qp LL O) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (R κ t : ℕ) (k : Fin d) {H : W.DD T} (h : IsHorTr W T b sol R κ k H) :
    IsHorTr W T b sol R (κ + t) k (lA W ^ t • H) := by
  obtain ⟨y, hy, rfl⟩ := h
  refine ⟨fun r m => ((PD.p : ℕ) : O) ^ t * y r m, fun r hr m => ?_, ?_⟩
  · rw [map_mul, map_pow, map_natCast, hy r hr m, pow_add]; ring
  · rw [lA_smul_eq, Finset.smul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [vecB_smul, smul_comm]

variable [IsDomain O]

theorem horTr_unique (hinj : Function.Injective (algebraMap O LL)) (T : LocLat G Qp LL O) {d : ℕ}
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (R κ : ℕ) (k : Fin d) {H H' : W.DD T}
    (h : IsHorTr W T b sol R κ k H) (h' : IsHorTr W T b sol R κ k H') : H = H' := by
  obtain ⟨y, hy, rfl⟩ := h
  obtain ⟨y', hy', rfl⟩ := h'
  refine Finset.sum_congr rfl fun r hr => ?_
  have : y r = y' r := funext fun m => hinj ((hy r (Finset.mem_range.1 hr) m).trans
    (hy' r (Finset.mem_range.1 hr) m).symm)
  rw [this]

def RV (T : LocLat G Qp LL O) (c' : ZMod n) (e : ℕ) (Λ : LetA O n) {d : ℕ} (κ : ℕ)
    (Hh : Fin d → W.DD T) (x : W.DD T) (f : Fin d → W.EE) : Prop :=
  ∃ (κ' : ℕ) (a : Fin d → LetA O n),
    (∀ k, a k ∈ W.AΔ ∧ algebraMap (LetA O n) W.EE Λ * f k = algebraMap (LetA O n) W.EE (a k)) ∧
    InFP W T c' e (W.π₀ * Λ ^ 2) (lA W ^ κ' • (lA W ^ κ • Λ • x - ∑ k, a k • ((W.φD T) ^ e) (Hh k)))

theorem repVV_iff (T : LocLat G Qp LL O) (c' : ZMod n) (e M : ℕ) (Λ : LetA O n) {d : ℕ}
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (x : W.DD T) (f : Fin d → W.EE) :
    RepVV W T c' e M Λ b sol x f ↔
      ∃ κ Hh, (∀ k, IsHorTr W T b sol M κ k (Hh k)) ∧ RV W T c' e Λ κ Hh x f := by
  constructor
  · rintro ⟨κ, κ', Hh, a, h1, h2, h3⟩
    exact ⟨κ, Hh, h1, κ', a, h2, h3⟩
  · rintro ⟨κ, Hh, h1, κ', a, h2, h3⟩
    exact ⟨κ, κ', Hh, a, h1, h2, h3⟩

theorem rv_up (T : LocLat G Qp LL O) (c' : ZMod n) (e : ℕ) (Λ : LetA O n) {d : ℕ} (κ t : ℕ)
    (Hh : Fin d → W.DD T) (x : W.DD T) (f : Fin d → W.EE) (h : RV W T c' e Λ κ Hh x f) :
    RV W T c' e Λ (κ + t) (fun k => lA W ^ t • Hh k) x f := by
  obtain ⟨κ', a, ha, hP⟩ := h
  refine ⟨κ', a, ha, ?_⟩
  have e1 : lA W ^ κ' • (lA W ^ (κ + t) • Λ • x - ∑ k, a k • ((W.φD T) ^ e) (lA W ^ t • Hh k)) =
      lA W ^ t • (lA W ^ κ' • (lA W ^ κ • Λ • x - ∑ k, a k • ((W.φD T) ^ e) (Hh k))) := by
    simp only [φpow_lA, smul_sub, Finset.smul_sum, smul_smul, pow_add]
    congr 1
    · ring_nf
    · refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      ring
  rw [e1]
  exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' e _ (lA_mem W t) hP

theorem rv_add (T : LocLat G Qp LL O) (c' : ZMod n) (e : ℕ) (Λ : LetA O n) {d : ℕ} (κ : ℕ)
    (Hh : Fin d → W.DD T) (x y : W.DD T) (f g : Fin d → W.EE) (hx : RV W T c' e Λ κ Hh x f)
    (hy : RV W T c' e Λ κ Hh y g) : RV W T c' e Λ κ Hh (x + y) (f + g) := by
  obtain ⟨κ₁, a₁, ha₁, hP₁⟩ := hx
  obtain ⟨κ₂, a₂, ha₂, hP₂⟩ := hy
  refine ⟨κ₁ + κ₂, a₁ + a₂, fun k => ⟨W.AΔ.add_mem (ha₁ k).1 (ha₂ k).1, ?_⟩, ?_⟩
  · rw [Pi.add_apply, mul_add, (ha₁ k).2, (ha₂ k).2, Pi.add_apply, map_add]
  · have e1 : lA W ^ (κ₁ + κ₂) • (lA W ^ κ • Λ • (x + y) - ∑ k, (a₁ + a₂) k • ((W.φD T) ^ e) (Hh k)) =
        lA W ^ κ₂ • (lA W ^ κ₁ • (lA W ^ κ • Λ • x - ∑ k, a₁ k • ((W.φD T) ^ e) (Hh k))) +
        lA W ^ κ₁ • (lA W ^ κ₂ • (lA W ^ κ • Λ • y - ∑ k, a₂ k • ((W.φD T) ^ e) (Hh k))) := by
      rw [lA_smul_smul, lA_smul_smul, add_comm κ₂ κ₁, ← smul_add]
      congr 1
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, smul_add]
      abel
    rw [e1]
    exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_add W T c' e _
      (Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' e _ (lA_mem W _) hP₁)
      (Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' e _ (lA_mem W _) hP₂)

theorem rv_smul (T : LocLat G Qp LL O) (c' : ZMod n) (e : ℕ) (Λ : LetA O n) {d : ℕ} (κ : ℕ)
    (Hh : Fin d → W.DD T) (x : W.DD T) (f : Fin d → W.EE) {c : LetA O n} (hc : c ∈ W.AΔ)
    (hx : RV W T c' e Λ κ Hh x f) :
    RV W T c' e Λ κ Hh (c • x) (fun k => algebraMap (LetA O n) W.EE c * f k) := by
  obtain ⟨κ₁, a₁, ha₁, hP₁⟩ := hx
  refine ⟨κ₁, fun k => c * a₁ k, fun k => ⟨W.AΔ.mul_mem hc (ha₁ k).1, ?_⟩, ?_⟩
  · rw [mul_left_comm, (ha₁ k).2, ← map_mul]
  · have e1 : lA W ^ κ₁ • (lA W ^ κ • Λ • (c • x) - ∑ k, (c * a₁ k) • ((W.φD T) ^ e) (Hh k)) =
        c • (lA W ^ κ₁ • (lA W ^ κ • Λ • x - ∑ k, a₁ k • ((W.φD T) ^ e) (Hh k))) := by
      simp only [smul_sub, Finset.smul_sum, mul_smul]
      congr 1
      · rw [smul_comm c (lA W ^ κ₁), smul_comm c (lA W ^ κ), smul_comm c Λ]
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_comm c (lA W ^ κ₁)]
    rw [e1]
    exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' e _ hc hP₁

theorem repVV_add (hinj : Function.Injective (algebraMap O LL)) (T : LocLat G Qp LL O) (c' : ZMod n)
    (e M : ℕ) (Λ : LetA O n) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (x y : W.DD T) (f g : Fin d → W.EE) (hx : RepVV W T c' e M Λ b sol x f)
    (hy : RepVV W T c' e M Λ b sol y g) : RepVV W T c' e M Λ b sol (x + y) (f + g) := by
  rw [repVV_iff] at hx hy ⊢
  obtain ⟨κ₁, H₁, hH₁, hR₁⟩ := hx
  obtain ⟨κ₂, H₂, hH₂, hR₂⟩ := hy
  have h1 := rv_up W T c' e Λ κ₁ κ₂ H₁ x f hR₁
  have h2 := rv_up W T c' e Λ κ₂ κ₁ H₂ y g hR₂
  have hH : ∀ k, lA W ^ κ₂ • H₁ k = lA W ^ κ₁ • H₂ k := fun k =>
    horTr_unique W hinj T b sol M _ k (horTr_scale W T b sol M κ₁ κ₂ k (hH₁ k))
      (by rw [add_comm]; exact horTr_scale W T b sol M κ₂ κ₁ k (hH₂ k))
  rw [show (fun k => lA W ^ κ₁ • H₂ k) = fun k => lA W ^ κ₂ • H₁ k from funext fun k => (hH k).symm,
    add_comm κ₂ κ₁] at h2
  exact ⟨κ₁ + κ₂, _, fun k => horTr_scale W T b sol M κ₁ κ₂ k (hH₁ k), rv_add W T c' e Λ _ _ x y f g h1 h2⟩

theorem repVV_smul (T : LocLat G Qp LL O) (c' : ZMod n) (e M : ℕ) (Λ : LetA O n) {d : ℕ}
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (x : W.DD T) (f : Fin d → W.EE)
    {c : LetA O n} (hc : c ∈ W.AΔ) (hx : RepVV W T c' e M Λ b sol x f) :
    RepVV W T c' e M Λ b sol (c • x) (fun k => algebraMap (LetA O n) W.EE c * f k) := by
  rw [repVV_iff] at hx ⊢
  obtain ⟨κ, H, hH, hR⟩ := hx
  exact ⟨κ, H, hH, rv_smul W T c' e Λ κ H x f hc hR⟩

theorem repVV_sub (hinj : Function.Injective (algebraMap O LL)) (T : LocLat G Qp LL O) (c' : ZMod n)
    (e M : ℕ) (Λ : LetA O n) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (x y : W.DD T) (f g : Fin d → W.EE) (hx : RepVV W T c' e M Λ b sol x f)
    (hy : RepVV W T c' e M Λ b sol y g) : RepVV W T c' e M Λ b sol (x - y) (f - g) := by
  have h := repVV_smul W T c' e M Λ b sol y g (W.AΔ.neg_mem W.AΔ.one_mem) hy
  simp only [map_neg, map_one, neg_one_mul, neg_smul, one_smul] at h
  have := repVV_add W hinj T c' e M Λ b sol x (-y) f (fun k => -g k) hx h
  rwa [← sub_eq_add_neg, show f + (fun k => -g k) = f - g from by funext k; simp [sub_eq_add_neg]] at this

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup

variable [IsDomain O]

theorem horTr_exists (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O) (hTc : IsCrys PD T.ρ)
    (c' : ZMod n) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T c' b sol)
    (M : ℕ) : ∃ κ : ℕ, ∃ Hh : Fin d → W.DD T, ∀ k, IsHorTr W T b sol M κ k (Hh k) := by
  have hl : 2 ≤ PD.p := PD.hp.two_le
  have hHc := hH hCA T hTc c'
  have hBd := (hHc.2.2.2.2 d b hb.1 sol hb.2).1
  have h4 := hHc.2.2.2.1
  choose g hg using fun k r m => Formalism.MainNotions.UnusedSlot80.Relay2.int_of_bd W hO2 r (h4 r) _ (hBd k r m)
  refine ⟨Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p M, fun k => ∑ r ∈ Finset.range M, W.π₀ ^ r •
    Formalism.MainNotions.LiftingTheory.vecB W T b (fun m => ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p M -
      Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) * g k r m), fun k => ⟨_, fun r hr m => ?_, rfl⟩⟩
  have hle := Formalism.MainNotions.UnusedSlot80.Relay2.Ex_mono PD.p hl hr.le
  simp only [map_mul, map_pow, map_natCast, hg]
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

theorem horTr_mem (T : LocLat G Qp LL O) (c' : ZMod n) {d : ℕ} (b : Fin d → W.DD T)
    (sol : Fin d → ℕ → Fin d → LL) (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (hπ : W.π₀ ∈ W.AΔ)
    (R κ e : ℕ) (k : Fin d) {H : W.DD T} (h : IsHorTr W T b sol R κ k H) :
    ((W.φD T) ^ e) H ∈ Pp W T c' e := by
  obtain ⟨y, -, rfl⟩ := h
  rw [map_sum]
  refine AddSubgroup.sum_mem _ fun r _ => ?_
  rw [Formalism.MainNotions.UnusedSlot80.Relay2.φpow_smul]
  refine Formalism.MainNotions.UnusedSlot80.Relay2.Pp_gen W T c' e (Formalism.MainNotions.UnusedSlot80.PhiPowers.φA_pow_mem_AΔ W (W.AΔ.pow_mem hπ r) e) ?_
  unfold Formalism.MainNotions.LiftingTheory.vecB
  refine ⟨?_, ?_⟩
  · refine ⟨(W.N T).sum_mem fun m _ => (W.N T).smul_of_tower_mem _ ((hb.1 m).1.1), fun δ hδ => ?_⟩
    rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [map_smul, (hb.1 m).1.2 δ hδ]
  · refine ⟨∑ m, y r m • b m, (W.N T).sum_mem fun m _ => (W.N T).smul_of_tower_mem _ ((hb.1 m).1.1), ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_comm, Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T c' (hb.1 m).2]

theorem yM_gen (hTr : Formalism.MainNotions.LiftingTheory.coreTr W) (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (hπ : W.π₀ ∈ W.AΔ) (h5p : 5 ≤ PD.p)
    (A : ArcP n) (hA : A.OK) (a : ZMod n) (e : ℕ) :
    ∃ ν ∈ W.AΔ, ((W.φA ^ e) W.π₀) ^ A.M PD.p = W.π₀ * abelian₂ W A a e ^ 2 * ν := by
  obtain ⟨u, hu, u', -, -, hT⟩ := (hTr hCA).2.1 e (A.M PD.p)
  have hlt := Formalism.MainNotions.UnusedSlot80.ArcC.two_h_lt A h5p
  have hM : 1 ≤ A.M PD.p := by unfold ArcP.M; exact Nat.le_add_left 1 _
  have hle : ∀ s, 2 * A.Hs a e s ≤ (PD.p - 1) * A.M PD.p := fun s => by
    have := Formalism.MainNotions.UnusedSlot80.ArcC.hs_le_h A hA a e s; omega
  refine ⟨u * W.π₀ ^ (A.M PD.p - 1) * ∏ s ∈ Finset.range e, ps W s ^ ((PD.p - 1) * A.M PD.p - 2 * A.Hs a e s),
    W.AΔ.mul_mem (W.AΔ.mul_mem hu (W.AΔ.pow_mem hπ _)) (W.AΔ.prod_mem fun s _ =>
      W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.PhiPowers.ps_mem_AΔ W hπ s) _), ?_⟩
  rw [hT]
  have e1 : W.π₀ ^ A.M PD.p = W.π₀ * W.π₀ ^ (A.M PD.p - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hM]
  have e2 : ∏ k ∈ Finset.range e, Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * A.M PD.p) =
      abelian₂ W A a e ^ 2 * ∏ s ∈ Finset.range e, ps W s ^ ((PD.p - 1) * A.M PD.p - 2 * A.Hs a e s) := by
    unfold abelian₂
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Formalism.MainNotions.UnusedSlot80.ArcC.pk_eq_ps, ← pow_mul, ← pow_add]
    congr 1
    have := hle s
    omega
  rw [e1, e2]
  ring

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O]

theorem secOfP' (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W) (hH : Formalism.MainNotions.LiftingTheory.coreH W)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (h5p : 5 ≤ PD.p) (A : ArcP n) (hA : A.OK)
    (c' : ZMod n) (e : ℕ) (T : LocLat G Qp LL O) (hTc : IsCrys PD T.ρ) {d : ℕ}
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T c' b sol) (x : W.DD T)
    (hx : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • x)) :
    ∃ (κ : ℕ) (f : Fin d → W.EE), RepVV W T c' e (A.M PD.p) (abelian₂ W A (c' + (e : ZMod n)) e) b sol
      (lA W ^ κ • x) f ∧ ∀ k, InFr W (c' + (e : ZMod n)) 1 (abelian₂ W A (c' + (e : ZMod n)) e) (f k) := by
  have hl : 2 ≤ PD.p := PD.hp.two_le
  obtain ⟨yP, hyP, hyx⟩ := hx
  rw [one_smul] at hyx
  obtain ⟨β₀, hβ₀, hyβ⟩ := Formalism.MainNotions.UnusedSlot80.ArcF.Pp_repr W T c' e b hb.1 yP hyP
  have hbl : ∀ m, (letE c' : LetA O n) • b m = b m := fun m =>
    Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T c' (hb.1.1 m).2
  have hφl : ∀ m, (letE (c' + (e : ZMod n)) : LetA O n) • ((W.φD T) ^ e) (b m) = ((W.φD T) ^ e) (b m) :=
    fun m => φD_pow_letter W T c' (b m) (hbl m) e
  set Λ : LetA O n := abelian₂ W A (c' + (e : ZMod n)) e with hΛdef
  let β : Fin d → LetA O n := fun m => letE (c' + (e : ZMod n)) * β₀ m
  have hβ : ∀ m, β m ∈ W.AΔ := fun m => W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W _) (hβ₀ m)
  have hΛx : Λ • x = ∑ m, β m • ((W.φD T) ^ e) (b m) := by
    rw [hyx, hyβ]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [β, mul_smul]
    rw [smul_comm, hφl]
  have hHc := hH hCA T hTc c'
  have hH5 := hHc.2.2.2.2 d b hb.1 sol hb.2
  have h4 := hHc.2.2.2.1
  choose g hg using fun k r m => Formalism.MainNotions.UnusedSlot80.Relay2.int_of_bd W hO2 r (h4 r) _ (hH5.1 k r m)
  choose g' hg' using fun r k m => Formalism.MainNotions.UnusedSlot80.Relay2.int_of_bd W hO2 r (h4 r) _ (hH5.2 k m r)
  set M : ℕ := A.M PD.p with hMdef
  let κ : ℕ := Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p M
  let yy : Fin d → ℕ → Fin d → O := fun k r m =>
    ((PD.p : ℕ) : O) ^ (κ - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) * g k r m
  let zz : ℕ → Fin d → Fin d → O := fun r k m =>
    ((PD.p : ℕ) : O) ^ (κ - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) * g' r k m
  have hyy : ∀ k, ∀ r < M, ∀ m, algebraMap O LL (yy k r m) = (PD.p : LL) ^ κ * sol k r m := by
    intro k r hr m
    have hle := Formalism.MainNotions.UnusedSlot80.Relay2.Ex_mono PD.p hl hr.le
    simp only [yy, map_mul, map_pow, map_natCast, hg]
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  have hzz : ∀ r < M, ∀ k m, algebraMap O LL (zz r k m) = (PD.p : LL) ^ κ *
      PowerSeries.coeff r ((Matrix.of fun m' k' => PowerSeries.mk fun r' => sol k' r' m' :
        Matrix (Fin d) (Fin d) (PowerSeries LL))⁻¹ k m) := by
    intro r hr k m
    have hle := Formalism.MainNotions.UnusedSlot80.Relay2.Ex_mono PD.p hl hr.le
    simp only [zz, map_mul, map_pow, map_natCast, hg']
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  set Y : LetA O n := (W.φA ^ e) W.π₀ with hYdef
  have hY : Y ∈ W.AΔ := φA_pow_mem_AΔ W hR.1 e
  set D : LetA O n := W.π₀ * Λ ^ 2 with hDdef
  obtain ⟨ν, hν, hYM⟩ := yM_gen W hTr hCA hR.1 h5p A hA (c' + (e : ZMod n)) e
  have hYM' : Y ^ M = D * ν := by rw [hYdef, hMdef, hYM]
  choose ρ hρ using fun m m' =>
    Formalism.MainNotions.UnusedSlot80.ArcF.frame_inv_poly hinj sol (fun k => (hb.2 k).2) M κ yy hyy zz hzz Y m m'
  let HY : Fin d → Fin d → LetA O n := fun m k =>
    ∑ r ∈ Finset.range M, algebraMap O (LetA O n) (yy k r m) * Y ^ r
  let GY : Fin d → Fin d → LetA O n := fun k m' =>
    ∑ r ∈ Finset.range M, algebraMap O (LetA O n) (zz r k m') * Y ^ r
  have hGY : ∀ k m', GY k m' ∈ W.AΔ := fun k m' => W.AΔ.sum_mem fun r _ =>
    W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) (W.AΔ.pow_mem hY r)
  let aa : Fin d → LetA O n := fun k => ∑ m', GY k m' * β m'
  have haa : ∀ k, aa k ∈ W.AΔ := fun k => W.AΔ.sum_mem fun m' _ => W.AΔ.mul_mem (hGY k m') (hβ m')
  have haal : ∀ k, letE (c' + (e : ZMod n)) * 1 * aa k = aa k := by
    intro k
    simp only [aa, mul_one, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    simp only [β]
    linear_combination (GY k m' * β₀ m') * (letE_mul_self (O := O) (c' + (e : ZMod n)))
  obtain ⟨U, hU⟩ := lam_unit W hR A (c' + (e : ZMod n)) e
  have hcoef : ∀ k, algebraMap (LetA O n) W.EE Λ *
      (((U⁻¹ : W.EEˣ) : W.EE) * algebraMap (LetA O n) W.EE (aa k)) = algebraMap (LetA O n) W.EE (aa k) := by
    intro k
    rw [← hU, ← mul_assoc, Units.mul_inv, one_mul]
  let w : Fin d → LetA O n := fun m => -(ν * ∑ m', Polynomial.aeval Y (ρ m m') * β m')
  have hw : ∀ m, w m ∈ W.AΔ := fun m => W.AΔ.neg_mem (W.AΔ.mul_mem hν (W.AΔ.sum_mem fun m' _ =>
      W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.ArcF.aeval_mem_AΔ W hY _) (hβ m')))
  have hkey : ∀ m, lA W ^ κ * lA W ^ κ * β m - ∑ k, aa k * HY m k = D * w m := by
    intro m
    have A2 : ∑ k, aa k * HY m k = ∑ m', (∑ k, HY m k * GY k m') * β m' := by
      simp only [aa, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun m' _ => Finset.sum_congr rfl fun k _ => by ring
    have h1 : ∀ m', (∑ k, HY m k * GY k m') * β m' =
        lA W ^ κ * lA W ^ κ * ((if m = m' then 1 else 0) * β m') +
          Y ^ M * (Polynomial.aeval Y (ρ m m') * β m') := by
      intro m'
      have := hρ m m'
      simp only [HY, GY] at this ⊢
      rw [this, map_mul, map_pow, map_natCast, apply_ite (algebraMap O (LetA O n)), map_one, map_zero]
      unfold lA
      split_ifs <;> ring
    rw [A2, Finset.sum_congr rfl fun m' _ => h1 m', Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, w]
    rw [hYM']
    ring
  refine ⟨κ, fun k => ((U⁻¹ : W.EEˣ) : W.EE) * algebraMap (LetA O n) W.EE (aa k),
    ⟨κ, 0, fun k => ∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r), aa,
      fun k => ⟨yy k, hyy k, rfl⟩, fun k => ⟨haa k, hcoef k⟩, ?_⟩,
    fun k => ⟨aa k, haa k, by rw [hcoef k, haal k]⟩⟩
  have hsum : ∑ k, aa k • ((W.φD T) ^ e)
      (∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r)) =
      ∑ m, (∑ k, aa k * HY m k) • ((W.φD T) ^ e) (b m) := by
    simp only [Formalism.MainNotions.UnusedSlot80.ArcF.phi_trunc, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    simp only [HY, ← hYdef]
    congr 1
    refine Finset.sum_congr rfl fun r _ => mul_comm _ _
  have hfin : lA W ^ 0 • (lA W ^ κ • Λ • (lA W ^ κ • x) - ∑ k, aa k • ((W.φD T) ^ e)
        (∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yy k r))) =
      D • ∑ m, w m • ((W.φD T) ^ e) (b m) := by
    rw [pow_zero, one_smul, hsum, smul_comm Λ, hΛx]
    simp only [Finset.smul_sum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [smul_smul]
    rw [← sub_smul, ← hkey m]
    congr 1
    ring
  rw [hfin]
  exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_of_mem W T c' e _ (AddSubgroup.sum_mem _ fun m _ =>
    Formalism.MainNotions.UnusedSlot80.Relay2.Pp_gen W T c' e (hw m) (hb.1.1 m))

theorem pOfSec' (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hCA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (A : ArcP n) (c' : ZMod n) (e M : ℕ) (T : LocLat G Qp LL O) (hTc : IsCrys PD T.ρ) {d : ℕ}
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T c' b sol) (f : Fin d → W.EE)
    (hf : ∀ k, InFr W (c' + (e : ZMod n)) 1 (abelian₂ W A (c' + (e : ZMod n)) e) (f k)) :
    ∃ (κ : ℕ) (x : W.DD T), InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • x) ∧
      RepVV W T c' e M (abelian₂ W A (c' + (e : ZMod n)) e) b sol x (fun k => lE W κ * f k) := by
  obtain ⟨κ, Hh, hHh⟩ := horTr_exists W hO2 hH hCA T hTc c' b sol hb M
  choose u hu hfu using hf
  set Λ : LetA O n := abelian₂ W A (c' + (e : ZMod n)) e with hΛdef
  obtain ⟨U, hU⟩ := lam_unit W hR A (c' + (e : ZMod n)) e
  let aa : Fin d → LetA O n := fun k => letE (c' + (e : ZMod n)) * 1 * u k
  have haa : ∀ k, aa k ∈ W.AΔ := fun k =>
    W.AΔ.mul_mem (W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W _) W.AΔ.one_mem) (hu k)
  set z : W.DD T := ∑ k, aa k • ((W.φD T) ^ e) (Hh k) with hz
  have hzP : z ∈ Pp W T c' e := AddSubgroup.sum_mem _ fun k _ =>
    Formalism.MainNotions.UnusedSlot80.Relay2.Pp_smul W T c' e (haa k) _ (horTr_mem W T c' b sol hb.1 hR.1 M κ e k (hHh k))
  have hΛz : Λ • (((U⁻¹ : W.EEˣ) : W.EE) • z) = z := by
    rw [← algebraMap_smul W.EE Λ, ← hU, smul_smul, Units.mul_inv, one_smul]
  refine ⟨κ, ((U⁻¹ : W.EEˣ) : W.EE) • z, ⟨z, hzP, by rw [hΛz, one_smul]⟩, κ, 0, Hh,
    fun k => lA W ^ κ * aa k, hHh, fun k => ⟨W.AΔ.mul_mem (lA_mem W κ) (haa k), ?_⟩, ?_⟩
  · rw [mul_left_comm, hfu k]
    show lE W κ * _ = algebraMap (LetA O n) W.EE (lA W ^ κ * aa k)
    rw [map_mul (algebraMap (LetA O n) W.EE) (lA W ^ κ), map_pow]
    unfold lE lA
    rw [map_natCast]
  · rw [hΛz, pow_zero, one_smul, hz]
    simp only [Finset.smul_sum, mul_smul, sub_self]
    exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_zero W T c' e _

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O]

theorem φ_Pp (T : LocLat G Qp LL O) (c' : ZMod n) (e : ℕ) :
    ∀ y ∈ Pp W T c' e, W.φD T y ∈ Pp W T c' (e + 1) := by
  refine Formalism.MainNotions.UnusedSlot80.Relay2.Pp_ind W T c' e _ (by simpa using (Pp W T c' (e + 1)).zero_mem)
    (fun x y hx hy => by rw [map_add]; exact (Pp W T c' (e + 1)).add_mem hx hy)
    (fun x hx => by rw [map_neg]; exact (Pp W T c' (e + 1)).neg_mem hx) ?_
  intro a ha x hx
  rw [φD_smulA, ← pow_apply_succ]
  exact Formalism.MainNotions.UnusedSlot80.Relay2.Pp_gen W T c' (e + 1) (Formalism.MainNotions.UnusedSlot80.ToolsR.φ_AΔ ha) hx

theorem φ_InFP (T : LocLat G Qp LL O) (c' : ZMod n) (e : ℕ) (F : LetA O n) {y : W.DD T}
    (h : InFP W T c' e F y) : InFP W T c' (e + 1) (W.φA F) (W.φD T y) := by
  obtain ⟨p, hp, rfl⟩ := h
  exact ⟨W.φD T p, φ_Pp W T c' e p hp, by rw [φD_smulA]⟩

theorem φA_lA (t : ℕ) : W.φA (lA W ^ t) = lA W ^ t := by
  rw [map_pow]; unfold lA; rw [map_natCast]

theorem φE_alg (a : LetA O n) : W.φE (algebraMap (LetA O n) W.EE a) = algebraMap (LetA O n) W.EE (W.φA a) :=
  W.φE_ext a

theorem φA_π₀ (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hp0 : ((PD.p : ℕ) : O) ≠ 0) :
    ∃ w ∈ W.AΔ, W.φA W.π₀ = w * W.π₀ * ps W 0 ^ (PD.p - 1) := by
  obtain ⟨-, w, hw⟩ := Formalism.MainNotions.UnusedSlot80.SatW.ring_clauses W hR
  have hq : (W.π₀ + ((PD.p : ℕ) : LetA O n)) = ps W 0 := by rw [ps_zero]; rfl
  rw [hq] at hw
  have hp0Δ : ps W 0 ∈ W.AΔ := ps_mem_AΔ W hR.1 0
  have hc : W.π₀ * ps W 0 ^ (PD.p - 1) ∈ W.AΔ := W.AΔ.mul_mem hR.1 (W.AΔ.pow_mem hp0Δ _)
  have hqP : Formalism.MainNotions.WachCoordinates.qP W = ps W 0 := by rw [ps_zero]; rfl
  have hc0 : ∀ i, (W.π₀ * ps W 0 ^ (PD.p - 1)) i ≠ 0 := by
    intro i
    rw [Pi.mul_apply, Pi.pow_apply, ← hqP]
    exact mul_ne_zero (Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_ne hR) (pow_ne_zero _ (Formalism.MainNotions.UnusedSlot80.ToolsR.q_component_ne_zero' hR hp0 i))
  refine ⟨(w : LetA O n), Formalism.MainNotions.UnusedSlot80.ToolsR.cancel_AΔ hc hc0 ?_, by rw [hw]⟩
  rw [show W.π₀ * ps W 0 ^ (PD.p - 1) * (w : LetA O n) = W.φA W.π₀ by rw [hw]; ring]
  exact Formalism.MainNotions.UnusedSlot80.ToolsR.φ_AΔ hR.1

theorem transport (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hp0 : ((PD.p : ℕ) : O) ≠ 0)
    (T : LocLat G Qp LL O) (A : ArcP n) (c' : ZMod n) (e M : ℕ) {d : ℕ} (b : Fin d → W.DD T)
    (sol : Fin d → ℕ → Fin d → LL) (x : W.DD T) (f : Fin d → W.EE)
    (hx : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • x))
    (hrep : RepVV W T c' e M (abelian₂ W A (c' + (e : ZMod n)) e) b sol x f)
    (hfr : ∀ k, InFr W (c' + (e : ZMod n)) 1 (abelian₂ W A (c' + (e : ZMod n)) e) (f k))
    (N : ℕ) (hN : A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0 ≤ N) {vv : LetA O n} (hv : vv ∈ W.AΔ) :
    InFP W T c' (e + 1) 1 (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) • ((ps W 0 ^ N * vv) • W.φD T x)) ∧
    RepVV W T c' (e + 1) M (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1)) b sol
      ((ps W 0 ^ N * vv) • W.φD T x)
      (fun k => algebraMap (LetA O n) W.EE (ps W 0 ^ N * vv) * W.φE (f k)) ∧
    ∀ k, InFr W (c' + ((e + 1 : ℕ) : ZMod n)) 1 (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1))
      (algebraMap (LetA O n) W.EE (ps W 0 ^ N * vv) * W.φE (f k)) := by
  set H : ℕ := A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0 with hHdef
  set Λ : LetA O n := abelian₂ W A (c' + (e : ZMod n)) e with hΛdef
  set u : LetA O n := ps W 0 ^ N * vv with hudef
  have hlam : abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) = ps W 0 ^ H * W.φA Λ := lam_succ W A c' e
  have hp0Δ : ps W 0 ∈ W.AΔ := ps_mem_AΔ W hR.1 0
  have huΔ : u ∈ W.AΔ := W.AΔ.mul_mem (W.AΔ.pow_mem hp0Δ N) hv
  have hupΔ : u * ps W 0 ^ H ∈ W.AΔ := W.AΔ.mul_mem huΔ (W.AΔ.pow_mem hp0Δ H)
  have hmain : ∀ z : W.DD T, abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) • (u • W.φD T z) =
      (u * ps W 0 ^ H) • W.φD T (Λ • z) := by
    intro z
    rw [hlam, φD_smulA, smul_smul, smul_smul]
    congr 1; ring
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨p, hp, hxp⟩ := hx
    rw [one_smul] at hxp
    refine ⟨(u * ps W 0 ^ H) • W.φD T p, Formalism.MainNotions.UnusedSlot80.Relay2.Pp_smul W T c' (e + 1) hupΔ _
      (φ_Pp W T c' e p hp), ?_⟩
    rw [one_smul, hmain, hxp]
  · rw [repVV_iff] at hrep ⊢
    obtain ⟨κ, Hh, hHh, κ', aa, haa, hP⟩ := hrep
    refine ⟨κ, Hh, hHh, κ', fun k => u * ps W 0 ^ H * W.φA (aa k), fun k =>
      ⟨W.AΔ.mul_mem hupΔ (Formalism.MainNotions.UnusedSlot80.ToolsR.φ_AΔ (haa k).1), ?_⟩, ?_⟩
    · have h1 := congrArg W.φE (haa k).2
      rw [map_mul, φE_alg, φE_alg] at h1
      rw [hlam, map_mul (algebraMap (LetA O n) W.EE) (u * ps W 0 ^ H), ← h1, hudef]
      simp only [map_mul]
      ring
    · obtain ⟨w, hw, hφπ⟩ := φA_π₀ W hR hp0
      have hP' := φ_InFP W T c' e _ hP
      obtain ⟨q, hq, hqe⟩ := hP'
      have hE : W.φD T (lA W ^ κ' • (lA W ^ κ • Λ • x - ∑ k, aa k • ((W.φD T) ^ e) (Hh k))) =
          lA W ^ κ' • (lA W ^ κ • W.φA Λ • W.φD T x - ∑ k, W.φA (aa k) • ((W.φD T) ^ (e + 1)) (Hh k)) := by
        rw [φD_smulA, φA_lA, map_sub, φD_smulA, φA_lA, φD_smulA, map_sum]
        congr 2
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [φD_smulA, pow_apply_succ]
      rw [hE] at hqe
      have hkey : lA W ^ κ' • (lA W ^ κ • abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) • (u • W.φD T x) -
          ∑ k, (u * ps W 0 ^ H * W.φA (aa k)) • ((W.φD T) ^ (e + 1)) (Hh k)) =
          (u * ps W 0 ^ H) • (lA W ^ κ' • (lA W ^ κ • W.φA Λ • W.φD T x -
            ∑ k, W.φA (aa k) • ((W.φD T) ^ (e + 1)) (Hh k))) := by
        rw [hlam]
        simp only [smul_sub, Finset.smul_sum, smul_smul]
        congr 1
        · congr 1; ring
        · refine Finset.sum_congr rfl fun k _ => ?_
          congr 1; ring
      rw [hkey, hqe, smul_smul]
      have hexp : H + H ≤ N + H + (PD.p - 1) := by omega
      refine ⟨(vv * w * ps W 0 ^ (N + H + (PD.p - 1) - (H + H))) • q,
        Formalism.MainNotions.UnusedSlot80.Relay2.Pp_smul W T c' (e + 1) (W.AΔ.mul_mem (W.AΔ.mul_mem hv hw)
          (W.AΔ.pow_mem hp0Δ _)) q hq, ?_⟩
      rw [smul_smul, hlam, map_mul, map_pow, hφπ]
      congr 1
      have e2 : ps W 0 ^ (N + H + (PD.p - 1)) = ps W 0 ^ (H + H) *
          ps W 0 ^ (N + H + (PD.p - 1) - (H + H)) := by
        rw [← pow_add, Nat.add_sub_cancel' hexp]
      rw [hudef]
      linear_combination (vv * w * W.π₀ * W.φA Λ ^ 2) * e2
  · intro k
    obtain ⟨t, ht, hft⟩ := hfr k
    refine ⟨u * ps W 0 ^ H * W.φA t, W.AΔ.mul_mem hupΔ (Formalism.MainNotions.UnusedSlot80.ToolsR.φ_AΔ ht), ?_⟩
    have h1 := congrArg W.φE hft
    rw [map_mul, φE_alg, φE_alg] at h1
    have hl : W.φA (letE (c' + (e : ZMod n)) : LetA O n) = letE (c' + ((e + 1 : ℕ) : ZMod n)) := by
      have := φA_letE W (c' + ((e + 1 : ℕ) : ZMod n))
      rwa [show c' + ((e + 1 : ℕ) : ZMod n) - 1 = c' + (e : ZMod n) by push_cast; ring] at this
    simp only [map_mul, mul_one, hl] at h1
    rw [hlam]
    simp only [map_mul, map_pow, mul_one]
    linear_combination (algebraMap (LetA O n) W.EE (ps W 0) ^ H * algebraMap (LetA O n) W.EE u) * h1

theorem piLam_of_sec (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hsatP : SATPcore W) (hCA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (T : LocLat G Qp LL O) (hTc : IsCrys PD T.ρ) (A : ArcP n) (c' : ZMod n) (e M : ℕ) {d : ℕ}
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b)
    (x : W.DD T) (hx : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • x)) (h : Fin d → W.EE)
    (hrep : RepVV W T c' e M (abelian₂ W A (c' + (e : ZMod n)) e) b sol x h)
    (hh : ∀ k, InFr W (c' + (e : ZMod n)) (W.π₀ * abelian₂ W A (c' + (e : ZMod n)) e) 1 (h k)) :
    InFP W T c' e (W.π₀ * abelian₂ W A (c' + (e : ZMod n)) e) x := by
  set Λ : LetA O n := abelian₂ W A (c' + (e : ZMod n)) e with hΛdef
  rw [repVV_iff] at hrep
  obtain ⟨κ, Hh, hHh, κ', aa, haa, hP⟩ := hrep
  choose u hu hhu using hh
  have haa' : ∀ k, aa k = W.π₀ * Λ ^ 2 * (letE (c' + (e : ZMod n)) * u k) := by
    intro k
    apply W.EE_inj
    rw [← (haa k).2]
    have := hhu k
    rw [map_one, one_mul] at this
    rw [this, ← map_mul]
    congr 1; ring
  have hS : InFP W T c' e (W.π₀ * Λ ^ 2) (∑ k, aa k • ((W.φD T) ^ e) (Hh k)) := by
    refine Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_sum W T c' e _ _ _ fun k _ => ?_
    rw [haa' k, mul_smul]
    exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_of_mem W T c' e _ (Formalism.MainNotions.UnusedSlot80.Relay2.Pp_smul W T c' e
      (W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W _) (hu k)) _
      (horTr_mem W T c' b sol hb hR.1 M κ e k (hHh k)))
  have h2 : InFP W T c' e (W.π₀ * Λ ^ 2) (Λ • (lA W ^ (κ + κ') • x)) := by
    have := Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_add W T c' e _ hP
      (Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' e _ (lA_mem W κ') hS)
    rw [smul_sub, sub_add_cancel] at this
    rwa [lA_smul_smul, smul_comm] at this
  obtain ⟨p, hp, hpe⟩ := h2
  have hcan : lA W ^ (κ + κ') • x = (W.π₀ * Λ) • p := by
    refine Formalism.MainNotions.UnusedSlot80.SatW.smul_cancel W T (lam_unit W hR A (c' + (e : ZMod n)) e) ?_
    rw [hpe, smul_smul]
    congr 1
    rw [← hΛdef]
    ring
  exact hsatP hCA T c' e (W.π₀ * Λ) Λ hTc (piLam_piPs W A _ e) (lam_piPs W A _ e) x hx
    ⟨κ + κ', p, hp, hcan⟩

theorem inN_of_piLam (hπ : W.π₀ ∈ W.AΔ) (T : LocLat G Qp LL O) (A : ArcP n) (c' : ZMod n) (e : ℕ)
    (hup : ∀ y ∈ Pp W T c' e, InFNc W T (c' + (e : ZMod n)) 1 (abelian₂ W A (c' + (e : ZMod n)) e • y))
    (x : W.DD T) (hx : InFP W T c' e (W.π₀ * abelian₂ W A (c' + (e : ZMod n)) e) x) :
    InFNc W T (c' + (e : ZMod n)) 1 x := by
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨y, hy, hyl, hye⟩ := hup p hp
  rw [one_smul] at hye
  refine ⟨W.π₀ • y, Formalism.MainNotions.UnusedSlot80.SatW.smul_mem_NΔ W T hπ hy, by rw [smul_comm, hyl], ?_⟩
  rw [one_smul, mul_smul, hye]

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O]

theorem γA_apply (g : W.Gam) (a : LetA O n) (i : ZMod n) : W.γA g a i = W.γ₀ g (a i) := rfl

theorem q_unit (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hp0 : ((PD.p : ℕ) : O) ≠ 0) :
    ∃ w : LetA O n, W.q = w * ps W 0 ∧ ∃ w' : LetA O n, w * w' = 1 ∧
      ∀ i, PowerSeries.constantCoeff (w' i) = 1 := by
  obtain ⟨w, hw⟩ := hR.2.2.2.2.1
  rw [Formalism.MainNotions.UnusedSlot80.SatW.Eat_π₀] at hw
  have hq : (W.π₀ + ((PD.p : ℕ) : LetA O n)) = ps W 0 := by rw [ps_zero]; rfl
  rw [hq] at hw
  refine ⟨w, hw, ((w⁻¹ : (LetA O n)ˣ) : LetA O n), Units.mul_inv w, fun i => ?_⟩
  have h1 : PowerSeries.constantCoeff (W.q i) =
      PowerSeries.constantCoeff ((w : LetA O n) i) * PowerSeries.constantCoeff (ps W 0 i) := by
    rw [hw, Pi.mul_apply, map_mul]
  rw [show W.q i = W.q₀ from rfl, Formalism.MainNotions.UnusedSlot80.ArcF.constantCoeff_q_zero_eq_p] at h1
  have h2 : PowerSeries.constantCoeff (ps W 0 i) = ((PD.p : ℕ) : O) := by
    rw [ps_zero]
    simp [LocWach.π₀, lA, Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR]
  rw [h2] at h1
  have hw1 : PowerSeries.constantCoeff ((w : LetA O n) i) = 1 := by
    have : ((PD.p : ℕ) : O) * (PowerSeries.constantCoeff ((w : LetA O n) i) - 1) = 0 := by
      linear_combination -h1
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hp0
    · exact sub_eq_zero.1 h
  have h3 : PowerSeries.constantCoeff ((w : LetA O n) i) *
      PowerSeries.constantCoeff (((w⁻¹ : (LetA O n)ˣ) : LetA O n) i) = 1 := by
    rw [← map_mul, ← Pi.mul_apply, Units.mul_inv]
    simp
  rwa [hw1, one_mul] at h3

theorem lam_zero (A : ArcP n) (a : ZMod n) : abelian₂ W A a 0 = 1 := by simp [abelian₂]

theorem cmpD_lam (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hp0 : ((PD.p : ℕ) : O) ≠ 0)
    (h5 : ∀ (T : LocLat G Qp LL O) (M h : ZMod n → ℕ), IsCrys PD T.ρ →
      Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h → Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h)
    (T : LocLat G Qp LL O) (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (A : ArcP n) (hA : A.OK) (c' : ZMod n)
    (hc' : c' ∈ A.cuts) (hT : Win W A T) :
    ∀ e : ℕ, ∃ t : ℕ, ∀ y, Formalism.MainNotions.LiftingTheory.InNΔi W T c' y →
      cmpD W T (abelian₂ W A (c' + (e : ZMod n)) e • ((W.φD T) ^ e) y) =
        ((PD.p : LL) ^ t) • ((Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V)) ^ e) (cmpD W T y) := by
  intro e
  induction e with
  | zero => exact ⟨0, fun y _ => by simp [lam_zero]⟩
  | succ e ih =>
    obtain ⟨t, ht⟩ := ih
    set H : ℕ := A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0 with hHdef
    refine ⟨H + t, fun y hy => ?_⟩
    set z : W.DD T := abelian₂ W A (c' + (e : ZMod n)) e • ((W.φD T) ^ e) y with hzdef
    obtain ⟨z', hz'N, hz'l, hzz'⟩ := Formalism.MainNotions.UnusedSlot80.ArcC.arc_up W hs hR h5 A hA c' hc' e T hT _
      (Formalism.MainNotions.UnusedSlot80.Relay2.Pp_phi W T c' e hy)
    rw [one_smul] at hzz'
    have hzN : z ∈ W.N T := by rw [hzdef, hzz']; exact hz'N.1
    have hzl : (letE (c' + (e : ZMod n)) : LetA O n) • z = z := by rw [hzdef, hzz']; exact hz'l
    have h5T := h5 T _ _ hT.1 (jumpsLet_of_win W A hA T hT)
    have hQ : W.Q = W.q := by simp [LocWach.Q, hs]
    set i : ZMod n := c' + ((e + 1 : ℕ) : ZMod n) with hidef
    have hzNl : z ∈ W.Nl T (i - 1) := by
      rw [show i - 1 = c' + (e : ZMod n) by rw [hidef]; push_cast; ring]
      exact ⟨z, hzN, by rw [LinearMap.smul_apply, LinearMap.id_apply]; exact hzl⟩
    have hM := h5T.1 i z hzNl
    rw [hQ] at hM
    have hMH : Mw A.G₀ A.S A.η (A.ty i) ≤ H := by
      have := Formalism.MainNotions.UnusedSlot80.ArcC.hs_ge A hA c' hc' (e + 1) (e + 1) (by omega) le_rfl
      rwa [Nat.sub_self] at this
    have hqN : W.q ^ H • W.φD T z ∈ W.N T := by
      obtain ⟨dd, hdd⟩ := Nat.exists_eq_add_of_le hMH
      rw [hdd, pow_add, mul_comm, mul_smul]
      exact (W.N T).smul_mem _ hM
    have hφl : (letE i : LetA O n) • W.φD T z = W.φD T z := by
      have := φD_pow_letter W T (c' + (e : ZMod n)) z hzl 1
      rw [pow_one] at this
      rwa [show c' + (e : ZMod n) + ((1 : ℕ) : ZMod n) = i by rw [hidef]; push_cast; ring] at this
    have hql : (letE i : LetA O n) • (W.q ^ H • W.φD T z) = W.q ^ H • W.φD T z := by
      rw [smul_comm, hφl]
    obtain ⟨w, hw, w', hww, hw'⟩ := q_unit W hR hp0
    have hp0w : ps W 0 = w' * W.q := by
      rw [hw, ← mul_assoc, mul_comm w', hww, one_mul]
    have e1 : abelian₂ W A i (e + 1) • ((W.φD T) ^ (e + 1)) y = w' ^ H • (W.q ^ H • W.φD T z) := by
      rw [hidef, lam_succ, pow_apply_succ, smul_smul, hzdef, φD_smulA, smul_smul, hp0w]
      unfold LamUp
      congr 1; ring
    have hk : W.Q ^ H • W.φD T ((⟨z, hzN⟩ : ↥(W.N T)) : W.DD T) ∈ W.N T := by rw [hQ]; exact hqN
    have e2 := h3.2.2 ⟨z, hzN⟩ H hk
    have e3 : (⟨W.Q ^ H • W.φD T z, hk⟩ : ↥(W.N T)) = ⟨W.q ^ H • W.φD T z, hqN⟩ := Subtype.ext (by show W.Q ^ H • W.φD T z = W.q ^ H • W.φD T z; rw [hQ])
    rw [e3] at e2
    rw [e1, Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T ((W.N T).smul_mem _ hqN),
      Formalism.MainNotions.UnusedSlot80.ArcF.cmp_smul_letter W T i _ _ hqN hql, e2, Pi.pow_apply, map_pow, hw', one_pow, map_one,
      one_smul, ← Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hzN, hzdef, ht y hy, map_smul, smul_smul, ← pow_add, pow_succ' _ e,
      Module.End.mul_apply]

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O]

theorem cmpD_sum (T : LocLat G Qp LL O) (a : ZMod n) {d : ℕ} (c : Fin d → LetA O n) (z : Fin d → W.DD T)
    (hz : ∀ m, z m ∈ W.N T) (hzl : ∀ m, (letE a : LetA O n) • z m = z m) :
    cmpD W T (∑ m, c m • z m) =
      ∑ m, algebraMap O LL (PowerSeries.constantCoeff (c m a)) • cmpD W T (z m) := by
  have hmem : ∀ m, c m • z m ∈ W.N T := fun m => (W.N T).smul_mem _ (hz m)
  have hs : ∑ m, c m • z m ∈ W.N T := (W.N T).sum_mem fun m _ => hmem m
  rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hs]
  have e : (⟨∑ m, c m • z m, hs⟩ : ↥(W.N T)) = ∑ m, (⟨c m • z m, hmem m⟩ : ↥(W.N T)) :=
    Subtype.ext (by simp)
  rw [e, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmp_smul_letter W T a (c m) (z m) (hz m) (hzl m),
    Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T (hz m)]

variable [NeZero n]

theorem indep_step (hinj : Function.Injective (algebraMap O LL)) (hV : Formalism.MainNotions.WachCoordinates.Br.ValRing (LL := LL) O v)
    (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hp0 : ((PD.p : ℕ) : O) ≠ 0)
    (h5 : ∀ (T : LocLat G Qp LL O) (M h : ZMod n → ℕ), IsCrys PD T.ρ →
      Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h → Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h)
    (T : LocLat G Qp LL O) (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀)
    (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts) (hT : Win W A T) {d : ℕ}
    (b : Fin d → W.DD T) (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (e : ℕ) (c : Fin d → LetA O n)
    (hc : ∀ m, c m ∈ W.AΔ) (hcl : ∀ m, letE (c' + (e : ZMod n)) * c m = c m)
    (h0 : ∑ m, c m • ((W.φD T) ^ e) (b m) = 0) :
    ∀ m, ∃ c₁ ∈ W.AΔ, letE (c' + (e : ZMod n)) * c₁ = c₁ ∧ c m = W.π₀ * c₁ := by
  set a : ZMod n := c' + (e : ZMod n) with hadef
  set Λ : LetA O n := abelian₂ W A a e with hΛdef
  have hz : ∀ m, InFNc W T a 1 (Λ • ((W.φD T) ^ e) (b m)) := fun m =>
    Formalism.MainNotions.UnusedSlot80.ArcC.arc_up W hs hR h5 A hA c' hc' e T hT _ (Formalism.MainNotions.UnusedSlot80.Relay2.Pp_phi W T c' e (hb.1 m))
  have hzN : ∀ m, Λ • ((W.φD T) ^ e) (b m) ∈ W.N T := fun m => by
    obtain ⟨y, hy, -, hye⟩ := hz m; rw [hye, one_smul]; exact hy.1
  have hzl : ∀ m, (letE a : LetA O n) • (Λ • ((W.φD T) ^ e) (b m)) = Λ • ((W.φD T) ^ e) (b m) := fun m => by
    obtain ⟨y, -, hyl, hye⟩ := hz m; rw [hye, one_smul]; exact hyl
  have hsum : ∑ m, c m • (Λ • ((W.φD T) ^ e) (b m)) = 0 := by
    rw [show ∑ m, c m • (Λ • ((W.φD T) ^ e) (b m)) = Λ • ∑ m, c m • ((W.φD T) ^ e) (b m) by
      rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun m _ => smul_comm _ _ _, h0, smul_zero]
  have hcmp := cmpD_sum W T a c _ hzN hzl
  rw [hsum] at hcmp
  have hc0 : cmpD W T (0 : W.DD T) = 0 := by
    rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T (W.N T).zero_mem]
    exact (W.cmp T).map_zero
  rw [hc0] at hcmp
  obtain ⟨t, ht⟩ := cmpD_lam W hs hR hp0 h5 T h3 A hA c' hc' hT e
  have hfb := (Formalism.MainNotions.UnusedSlot80.ArcF.frame_basis W hs hV T h3 (h5 T _ _ hT.1 (jumpsLet_of_win W A hA T hT))
    hmod c' e b hb).1
  have hrel : ∑ m, algebraMap O LL (PowerSeries.constantCoeff (c m a)) •
      dv W T e b (Pi.single m 1) = 0 := by
    have hpt : ((PD.p : LL) ^ t) ≠ 0 := pow_ne_zero _ (Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero W)
    rw [← hadef, ← hΛdef] at ht
    have e1 : ((PD.p : LL) ^ t) • ∑ m, algebraMap O LL (PowerSeries.constantCoeff (c m a)) •
        dv W T e b (Pi.single m 1) = 0 := by
      rw [hcmp, Finset.smul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [ht (b m) (hb.1 m), Formalism.MainNotions.UnusedSlot80.ArcF.dv_single, smul_comm]
    exact (smul_eq_zero.1 e1).resolve_left hpt
  have hcc : ∀ m i, PowerSeries.constantCoeff (c m i) = 0 := by
    intro m i
    by_cases hi : i = a
    · subst hi
      have := Fintype.linearIndependent_iff.1 hfb _ hrel m
      exact hinj (by rw [this, map_zero])
    · have := congrFun (hcl m) i
      rw [Pi.mul_apply, letE, Pi.single_eq_of_ne hi, zero_mul] at this
      rw [← this, map_zero]
  intro m
  have hinv : ∀ i, Formalism.MainNotions.WachCoordinates.Br.Inv1 W (c m i) := fun i δ hδ => by
    have := congrFun (hc m δ hδ) i
    rwa [γA_apply] at this
  choose f hf using fun i => Formalism.MainNotions.WachCoordinates.Br.ιOf_full hR (c m i) (hinv i)
  have hf0 : ∀ i, PowerSeries.constantCoeff (f i) = 0 := fun i => by
    rw [← Formalism.MainNotions.WachCoordinates.Br.ιOf_const hR, hf i, hcc m i]
  choose g hg using fun i => (PowerSeries.X_dvd_iff.2 (hf0 i))
  let c₂ : LetA O n := fun i => Formalism.MainNotions.WachCoordinates.Br.ιOf hR (g i)
  have hc₂ : c₂ ∈ W.AΔ := fun δ hδ => by
    funext i
    rw [γA_apply]
    exact Formalism.MainNotions.WachCoordinates.Br.ιOf_inv hR (g i) δ hδ
  have hcm : c m = W.π₀ * c₂ := by
    funext i
    rw [← hf i, hg i, map_mul, Formalism.MainNotions.WachCoordinates.Br.ιOf_X]
    rfl
  refine ⟨letE a * c₂, W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W a) hc₂,
    by rw [← mul_assoc, letE_mul_self], ?_⟩
  rw [← hcl m, hcm]
  ring

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O] [NeZero n]

theorem indep (hinj : Function.Injective (algebraMap O LL)) (hV : Formalism.MainNotions.WachCoordinates.Br.ValRing (LL := LL) O v)
    (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hp0 : ((PD.p : ℕ) : O) ≠ 0)
    (h5 : ∀ (T : LocLat G Qp LL O) (M h : ZMod n → ℕ), IsCrys PD T.ρ →
      Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h → Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h)
    (T : LocLat G Qp LL O) (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀)
    (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts) (hT : Win W A T) {d : ℕ}
    (b : Fin d → W.DD T) (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (e : ℕ) (c : Fin d → LetA O n)
    (hc : ∀ m, c m ∈ W.AΔ) (hcl : ∀ m, letE (c' + (e : ZMod n)) * c m = c m)
    (h0 : ∑ m, c m • ((W.φD T) ^ e) (b m) = 0) : ∀ m, c m = 0 := by
  obtain ⟨h3r, -⟩ := Formalism.MainNotions.UnusedSlot80.SatW.ring_clauses W hR
  have hπU := Formalism.MainNotions.UnusedSlot80.SatW.isUnit_EE_of_UPi W (Formalism.MainNotions.UnusedSlot80.SatW.UPi_π₀ W h3r)
  have key : ∀ k : ℕ, ∀ c : Fin d → LetA O n, (∀ m, c m ∈ W.AΔ) →
      (∀ m, letE (c' + (e : ZMod n)) * c m = c m) → ∑ m, c m • ((W.φD T) ^ e) (b m) = 0 →
      ∀ m, ∃ c₁ : LetA O n, c m = W.π₀ ^ k * c₁ := by
    intro k
    induction k with
    | zero => intro c _ _ _ m; exact ⟨c m, by simp⟩
    | succ k ih =>
      intro c hc hcl h0 m
      choose c₁ hc₁ hc₁l hcm using indep_step W hinj hV hs hR hp0 h5 T h3 hmod A hA c' hc' hT b hb e c hc hcl h0
      have h0' : ∑ m, c₁ m • ((W.φD T) ^ e) (b m) = 0 := by
        refine Formalism.MainNotions.UnusedSlot80.SatW.smul_cancel W T hπU ?_
        rw [smul_zero, Finset.smul_sum, ← h0]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [smul_smul, ← hcm m]
      obtain ⟨c₂, hc₂⟩ := ih c₁ hc₁ hc₁l h0' m
      exact ⟨c₂, by rw [hcm m, hc₂, pow_succ]; ring⟩
  intro m
  obtain ⟨w, -, hw⟩ := Formalism.MainNotions.UnusedSlot80.ToolsR.π₀_comp hR
  funext i
  refine PowerSeries.ext fun j => ?_
  obtain ⟨c₁, hc₁⟩ := key (j + 1) c hc hcl h0 m
  have hl : 2 ≤ PD.p := PD.hp.two_le
  have hdvd : (PowerSeries.X : PowerSeries O) ^ ((PD.p - 1) * (j + 1)) ∣ c m i := by
    rw [hc₁, Pi.mul_apply, Pi.pow_apply, show W.π₀ i = W.π₀₁ from rfl, hw, mul_pow, ← pow_mul]
    exact ⟨w ^ (j + 1) * c₁ i, by ring⟩
  rw [PowerSeries.X_pow_dvd_iff.1 hdvd j (by nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ PD.p)])]
  simp

omit [NeZero n] in

theorem frame_inv_poly' (hinj : Function.Injective (algebraMap O LL)) {d : ℕ}
    (sol : Fin d → ℕ → Fin d → LL) (hsol0 : ∀ k, sol k 0 = Pi.single k 1) (M κ : ℕ)
    (yy : Fin d → ℕ → Fin d → O) (hyy : ∀ k, ∀ r < M, ∀ m, algebraMap O LL (yy k r m) = (PD.p : LL) ^ κ * sol k r m)
    (zz : ℕ → Fin d → Fin d → O)
    (hzz : ∀ r < M, ∀ k m, algebraMap O LL (zz r k m) = (PD.p : LL) ^ κ *
      PowerSeries.coeff r ((Matrix.of fun m' k' => PowerSeries.mk fun r' => sol k' r' m' :
        Matrix (Fin d) (Fin d) (PowerSeries LL))⁻¹ k m))
    {R : Type} [CommRing R] [Algebra O R] (Y : R) (k k' : Fin d) :
    ∃ ρ : Polynomial O, ∑ m, (∑ r ∈ Finset.range M, algebraMap O R (zz r k m) * Y ^ r) *
        (∑ r ∈ Finset.range M, algebraMap O R (yy k' r m) * Y ^ r) =
      algebraMap O R (((PD.p : ℕ) : O) ^ (2 * κ) * if k = k' then 1 else 0) + Y ^ M * Polynomial.aeval Y ρ := by
  set Hps : Matrix (Fin d) (Fin d) (PowerSeries LL) :=
    Matrix.of fun m' k' => PowerSeries.mk fun r' => sol k' r' m' with hHps
  have hdet : IsUnit Hps.det := by
    rw [PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
    have h1 : (PowerSeries.constantCoeff : PowerSeries LL →+* LL).mapMatrix Hps = 1 := by
      ext i k
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hHps, Matrix.of_apply,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_mk, hsol0,
        Matrix.one_apply, Pi.single_apply]
    rw [h1, Matrix.det_one]
    exact isUnit_one
  have hinv : Hps⁻¹ * Hps = 1 := Matrix.nonsing_inv_mul Hps hdet
  have hcoef : ∀ t, ∑ m, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal t,
      PowerSeries.coeff x.1 (Hps⁻¹ k m) * sol k' x.2 m = if t = 0 ∧ k = k' then 1 else 0 := by
    intro t
    have h := congrArg (fun Q : Matrix (Fin d) (Fin d) (PowerSeries LL) => PowerSeries.coeff t (Q k k')) hinv
    simp only [Matrix.mul_apply, map_sum, PowerSeries.coeff_mul, hHps, Matrix.of_apply,
      PowerSeries.coeff_mk] at h
    rw [h, Matrix.one_apply]
    by_cases hm : k = k'
    · by_cases ht : t = 0
      · subst ht; simp [hm]
      · simp [hm, ht, PowerSeries.coeff_one]
    · simp [hm]
  let GP : Fin d → Polynomial O := fun m =>
    ∑ r ∈ Finset.range M, Polynomial.C (zz r k m) * Polynomial.X ^ r
  let HP : Fin d → Polynomial O := fun m =>
    ∑ r ∈ Finset.range M, Polynomial.C (yy k' r m) * Polynomial.X ^ r
  have hGPc : ∀ m i, (GP m).coeff i = if i < M then zz i k m else 0 := by
    intro m i
    simp only [GP, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_range]
  have hHPc : ∀ m i, (HP m).coeff i = if i < M then yy k' i m else 0 := by
    intro m i
    simp only [HP, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_range]
  set cst : O := ((PD.p : ℕ) : O) ^ (2 * κ) * if k = k' then 1 else 0 with hcst
  set Q : Polynomial O := ∑ m, GP m * HP m - Polynomial.C cst with hQdef
  have hQ : ∀ t < M, Q.coeff t = 0 := by
    intro t ht
    apply hinj
    rw [map_zero, hQdef, Polynomial.coeff_sub, Polynomial.finsetSum_coeff, Polynomial.coeff_C, map_sub,
      map_sum]
    have hk : ∀ m, algebraMap O LL ((GP m * HP m).coeff t) = (PD.p : LL) ^ (2 * κ) *
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal t, PowerSeries.coeff x.1 (Hps⁻¹ k m) * sol k' x.2 m := by
      intro m
      rw [Polynomial.coeff_mul, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
      rw [hGPc, hHPc, if_pos (by omega), if_pos (by omega), map_mul, hzz x.1 (by omega),
        hyy k' x.2 (by omega)]
      ring
    rw [Finset.sum_congr rfl fun m _ => hk m, ← Finset.mul_sum, hcoef t, hcst]
    by_cases ht0 : t = 0
    · subst ht0
      by_cases hm : k = k' <;> simp [hm]
    · simp [ht0]
  obtain ⟨ρ, hρ⟩ := (Polynomial.X_pow_dvd_iff).2 hQ
  refine ⟨ρ, ?_⟩
  have h := congrArg (Polynomial.aeval Y) hρ
  simp only [hQdef, map_sub, map_sum, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, GP, HP,
    Polynomial.aeval_X] at h
  rw [← h]
  ring

theorem sec_unique (hinj : Function.Injective (algebraMap O LL)) (hV : Formalism.MainNotions.WachCoordinates.Br.ValRing (LL := LL) O v)
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hp0 : ((PD.p : ℕ) : O) ≠ 0)
    (h5 : ∀ (T : LocLat G Qp LL O) (M h : ZMod n → ℕ), IsCrys PD T.ρ →
      Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h → Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h)
    (hTr : Formalism.MainNotions.LiftingTheory.coreTr W) (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (h5p : 5 ≤ PD.p)
    (T : LocLat G Qp LL O) (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀)
    (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts) (hT : Win W A T) {d : ℕ}
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T c' b sol) (e : ℕ)
    (x : W.DD T) (f g : Fin d → W.EE)
    (hf : RepVV W T c' e (A.M PD.p) (abelian₂ W A (c' + (e : ZMod n)) e) b sol x f)
    (hg : RepVV W T c' e (A.M PD.p) (abelian₂ W A (c' + (e : ZMod n)) e) b sol x g)
    (hfr : ∀ k, InFr W (c' + (e : ZMod n)) 1 (abelian₂ W A (c' + (e : ZMod n)) e) (f k))
    (hgr : ∀ k, InFr W (c' + (e : ZMod n)) 1 (abelian₂ W A (c' + (e : ZMod n)) e) (g k)) :
    ∃ t : ℕ, ∀ k, InFr W (c' + (e : ZMod n)) (W.π₀ * abelian₂ W A (c' + (e : ZMod n)) e) 1
      (lE W t * (f k - g k)) := by
  have hl : 2 ≤ PD.p := PD.hp.two_le
  set a : ZMod n := c' + (e : ZMod n) with hadef
  set Λ : LetA O n := abelian₂ W A a e with hΛdef
  set M : ℕ := A.M PD.p with hMdef
  obtain ⟨U, hU⟩ := lam_unit W hR A a e
  have hΛc : ∀ y z : W.EE, algebraMap (LetA O n) W.EE Λ * y = algebraMap (LetA O n) W.EE Λ * z → y = z :=
    fun y z h => by
      have hU' : (U : W.EE) = algebraMap (LetA O n) W.EE Λ := hU
      rw [← hU'] at h
      have := congrArg (fun w => ((U⁻¹ : W.EEˣ) : W.EE) * w) h
      simpa only [← mul_assoc, Units.inv_mul, one_mul] using this
  have h0 := repVV_sub W hinj T c' e M Λ b sol x x f g hf hg
  rw [sub_self, repVV_iff] at h0
  obtain ⟨κ, Hh, hHh, hRV⟩ := h0
  set K : ℕ := κ + Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p M with hKdef
  have hRV' := rv_up W T c' e Λ κ (Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p M) Hh 0 (f - g) hRV
  obtain ⟨κ', aa, haa, hP⟩ := hRV'
  choose yy hyy hHe using fun k => horTr_scale W T b sol M κ (Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p M) k (hHh k)

  choose uf huf hfu using hfr
  choose ug hug hgu using hgr
  have haa_eq : ∀ k, aa k = letE a * (uf k - ug k) := by
    intro k
    apply W.EE_inj
    rw [← (haa k).2, Pi.sub_apply, mul_sub, hfu k, hgu k, ← map_sub]
    congr 1; ring
  have haal : ∀ k, letE a * aa k = aa k := by
    intro k; rw [haa_eq k, ← mul_assoc, letE_mul_self]

  simp only [smul_zero, zero_sub, smul_neg] at hP
  obtain ⟨p, hp, hpe⟩ := hP
  obtain ⟨δ, hδ, hpδ⟩ := Formalism.MainNotions.UnusedSlot80.ArcF.Pp_repr W T c' e b hb.1 p hp
  set Y : LetA O n := (W.φA ^ e) W.π₀ with hYdef
  have hY : Y ∈ W.AΔ := φA_pow_mem_AΔ W hR.1 e
  let HY : Fin d → Fin d → LetA O n := fun m k =>
    ∑ r ∈ Finset.range M, algebraMap O (LetA O n) (yy k r m) * Y ^ r
  have hφH : ∀ k, ((W.φD T) ^ e) (lA W ^ Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p M • Hh k) =
      ∑ m, HY m k • ((W.φD T) ^ e) (b m) := by
    intro k
    rw [hHe k, Formalism.MainNotions.UnusedSlot80.ArcF.phi_trunc]
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
    simp only [HY, ← hYdef]
    exact Finset.sum_congr rfl fun r _ => mul_comm _ _

  let E : Fin d → LetA O n := fun m => lA W ^ κ' * ∑ k, aa k * HY m k
  have hrel : ∑ m, (letE a * (E m + W.π₀ * Λ ^ 2 * δ m)) • ((W.φD T) ^ e) (b m) = 0 := by
    have h1 : lA W ^ κ' • ∑ k, aa k • ((W.φD T) ^ e) (lA W ^ Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p M • Hh k) =
        ∑ m, E m • ((W.φD T) ^ e) (b m) := by
      simp only [hφH, Finset.smul_sum, smul_smul, E]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.mul_sum, Finset.sum_smul]
    have h2 : ∑ m, (E m + W.π₀ * Λ ^ 2 * δ m) • ((W.φD T) ^ e) (b m) = 0 := by
      rw [show ∑ m, (E m + W.π₀ * Λ ^ 2 * δ m) • ((W.φD T) ^ e) (b m) =
          (∑ m, E m • ((W.φD T) ^ e) (b m)) + (W.π₀ * Λ ^ 2) • p by
        simp only [add_smul, Finset.sum_add_distrib, hpδ, Finset.smul_sum, mul_smul], ← h1, ← hpe,
        add_neg_cancel]
    simp only [mul_smul]
    rw [← Finset.smul_sum, h2, smul_zero]
  have hEl : ∀ m, letE a * E m = E m := by
    intro m
    simp only [E, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← haal k]; ring_nf; rw [sq, letE_mul_self]
  have hind := indep W hinj hV hs hR hp0 h5 T h3 hmod A hA c' hc' hT b hb.1 e _
    (fun m => W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W a)
      (W.AΔ.add_mem (W.AΔ.mul_mem (lA_mem W κ') (W.AΔ.sum_mem fun k _ => W.AΔ.mul_mem (haa k).1
        (W.AΔ.sum_mem fun r _ => W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) (W.AΔ.pow_mem hY r))))
        (W.AΔ.mul_mem (W.AΔ.mul_mem hR.1 (W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.ArcC.lam_mem_AΔ W hR.1 A a e) 2)) (hδ m))))
    (fun m => by rw [← mul_assoc, letE_mul_self]) hrel
  have hEm : ∀ m, E m = -(W.π₀ * Λ ^ 2 * (letE a * δ m)) := by
    intro m
    have := hind m
    rw [mul_add, hEl m] at this
    linear_combination this

  have hHc := hH hCA T hT.1 c'
  have hH5 := hHc.2.2.2.2 d b hb.1 sol hb.2
  have h4 := hHc.2.2.2.1
  choose g' hg' using fun r k m => Formalism.MainNotions.UnusedSlot80.Relay2.int_of_bd W hO2 r (h4 r) _ (hH5.2 k m r)
  let zz : ℕ → Fin d → Fin d → O := fun r k m =>
    ((PD.p : ℕ) : O) ^ (K - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) * g' r k m
  have hzz : ∀ r < M, ∀ k m, algebraMap O LL (zz r k m) = (PD.p : LL) ^ K *
      PowerSeries.coeff r ((Matrix.of fun m' k' => PowerSeries.mk fun r' => sol k' r' m' :
        Matrix (Fin d) (Fin d) (PowerSeries LL))⁻¹ k m) := by
    intro r hr k m
    have hle : Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r ≤ K :=
      (Formalism.MainNotions.UnusedSlot80.Relay2.Ex_mono PD.p hl hr.le).trans (Nat.le_add_left _ _)
    simp only [zz, map_mul, map_pow, map_natCast, hg']
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  choose ρ hρ using fun k k' =>
    frame_inv_poly' (PD := PD) hinj sol (fun k => (hb.2 k).2) M K yy hyy zz hzz Y k k'
  obtain ⟨ν, hν, hYM⟩ := yM_gen W hTr hCA hR.1 h5p A hA a e
  have hYM' : Y ^ M = W.π₀ * Λ ^ 2 * ν := by rw [hYdef, hMdef, hYM]
  let GY : Fin d → Fin d → LetA O n := fun k m =>
    ∑ r ∈ Finset.range M, algebraMap O (LetA O n) (zz r k m) * Y ^ r
  have hGY : ∀ k m, GY k m ∈ W.AΔ := fun k m => W.AΔ.sum_mem fun r _ =>
    W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) (W.AΔ.pow_mem hY r)
  have hpK : algebraMap O (LetA O n) (((PD.p : ℕ) : O) ^ (2 * K)) = lA W ^ (2 * K) := by
    rw [map_pow, map_natCast]; rfl
  refine ⟨κ' + 2 * K, fun k₀ => ?_⟩
  set θ : LetA O n := -(∑ m, GY k₀ m * (letE a * δ m)) -
    lA W ^ κ' * ν * ∑ k, aa k * Polynomial.aeval Y (ρ k₀ k) with hθ
  have hθΔ : θ ∈ W.AΔ := W.AΔ.sub_mem (W.AΔ.neg_mem (W.AΔ.sum_mem fun m _ => W.AΔ.mul_mem (hGY k₀ m)
      (W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W a) (hδ m))))
    (W.AΔ.mul_mem (W.AΔ.mul_mem (lA_mem W κ') hν) (W.AΔ.sum_mem fun k _ => W.AΔ.mul_mem (haa k).1
      (Formalism.MainNotions.UnusedSlot80.ArcF.aeval_mem_AΔ W hY _)))
  have hkey : lA W ^ (κ' + 2 * K) * aa k₀ = W.π₀ * Λ ^ 2 * θ := by
    have hS1 : ∑ m, GY k₀ m * E m = lA W ^ κ' * ∑ k, aa k * (∑ m, GY k₀ m * HY m k) := by
      simp only [E, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => by ring
    have hS2 : ∑ k, aa k * (∑ m, GY k₀ m * HY m k) =
        lA W ^ (2 * K) * aa k₀ + Y ^ M * ∑ k, aa k * Polynomial.aeval Y (ρ k₀ k) := by
      have : ∀ k, aa k * (∑ m, GY k₀ m * HY m k) =
          lA W ^ (2 * K) * ((if k₀ = k then 1 else 0) * aa k) + Y ^ M * (aa k * Polynomial.aeval Y (ρ k₀ k)) := by
        intro k
        have h := hρ k₀ k
        simp only [GY, HY] at h ⊢
        rw [h, map_mul, hpK, apply_ite (algebraMap O (LetA O n)), map_one, map_zero]
        ring
      rw [Finset.sum_congr rfl fun k _ => this k, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hS3 : ∑ m, GY k₀ m * E m = -(W.π₀ * Λ ^ 2 * ∑ m, GY k₀ m * (letE a * δ m)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun m _ => by rw [hEm m]; ring
    rw [hS1, hS2, hYM'] at hS3
    rw [hθ, pow_add]
    linear_combination hS3
  have hlet : ∀ k, algebraMap (LetA O n) W.EE (letE a) * (f - g) k = (f - g) k := by
    intro k
    apply hΛc
    rw [← mul_assoc, mul_comm (algebraMap (LetA O n) W.EE Λ), mul_assoc, (haa k).2, ← map_mul, haal k]
  have hX : letE a * ∑ m, GY k₀ m * (letE a * δ m) = ∑ m, GY k₀ m * (letE a * δ m) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    linear_combination (GY k₀ m * δ m) * (letE_mul_self (O := O) a)
  have hZ : letE a * ∑ k, aa k * Polynomial.aeval Y (ρ k₀ k) = ∑ k, aa k * Polynomial.aeval Y (ρ k₀ k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_assoc, haal k]
  have hθl : letE a * θ = θ := by
    rw [hθ]
    linear_combination -hX - (lA W ^ κ' * ν) * hZ
  refine ⟨θ, hθΔ, ?_⟩
  rw [map_one, one_mul]
  apply hΛc
  have hfg : algebraMap (LetA O n) W.EE Λ * (f k₀ - g k₀) = algebraMap (LetA O n) W.EE (aa k₀) := (haa k₀).2
  have hlE : lE W (κ' + 2 * K) = algebraMap (LetA O n) W.EE (lA W ^ (κ' + 2 * K)) := by
    unfold lE lA; rw [map_pow, map_natCast]
  calc algebraMap (LetA O n) W.EE Λ * (lE W (κ' + 2 * K) * (f k₀ - g k₀))
      = lE W (κ' + 2 * K) * (algebraMap (LetA O n) W.EE Λ * (f k₀ - g k₀)) := by ring
    _ = algebraMap (LetA O n) W.EE (lA W ^ (κ' + 2 * K) * aa k₀) := by rw [hfg, hlE, map_mul]
    _ = algebraMap (LetA O n) W.EE Λ * algebraMap (LetA O n) W.EE (letE a * (W.π₀ * Λ) * θ) := by
      rw [hkey, ← map_mul]
      refine congrArg (algebraMap (LetA O n) W.EE) ?_
      conv_lhs => rw [← hθl]
      ring

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

section
noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem tmul_mem_filV (x : V) {y : BdR} {a : ℤ} (hy : y ∈ PD.Fil a) :
    x ⊗ₜ[Qp] y ∈ FilV PD (LL := LL) (V := V) a :=
  ⟨x ⊗ₜ[Qp] (⟨y, hy⟩ : ↥((PD.Fil a).restrictScalars Qp)), by
    simp [TensorProduct.AlgebraTensorModule.map_tmul]⟩

theorem filV_exh (z : V ⊗[Qp] BdR) : ∃ a, z ∈ FilV PD (LL := LL) (V := V) a := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul x y =>
    obtain ⟨a, ha⟩ := PD.Fil_exh y
    exact ⟨a, tmul_mem_filV x ha⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, Submodule.add_mem _ (Formalism.MainNotions.UnusedSlot80.LevR.filV_anti (min_le_left a b) ha)
      (Formalism.MainNotions.UnusedSlot80.LevR.filV_anti (min_le_right a b) hb)⟩

theorem filV_sep (z : V ⊗[Qp] BdR) (h : ∀ a, z ∈ FilV PD (LL := LL) (V := V) a) : z = 0 := by
  have hfree : Module.Free Qp V := Module.Free.of_divisionRing Qp V
  let 𝔟 := Module.Free.chooseBasis Qp V
  let E := TensorProduct.equivFinsuppOfBasisLeft (N := BdR) 𝔟
  have hcoord : ∀ a, ∀ w ∈ FilV PD (LL := LL) (V := V) a, ∀ i, E w i ∈ PD.Fil a := by
    intro a w hw i
    obtain ⟨u, rfl⟩ := hw
    induction u using TensorProduct.induction_on with
    | zero => simp [(PD.Fil a).zero_mem]
    | tmul x y =>
      simp only [TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply, Submodule.coe_subtype]
      rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul]
      simp only [Finsupp.mapRange_apply]
      have : (𝔟.repr x i) • (y : BdR) = algebraMap Qp K (𝔟.repr x i) • (y : BdR) := by
        rw [algebraMap_smul]
      rw [this]
      exact (PD.Fil a).smul_mem _ y.2
    | add u₁ u₂ h₁ h₂ =>
      rw [map_add, map_add, Finsupp.add_apply]
      exact (PD.Fil a).add_mem h₁ h₂
  have hE : E z = 0 := by
    ext i
    exact PD.Fil_sep _ fun a => hcoord a z (h a) i
  exact E.injective (by rw [hE, map_zero])

end Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup

theorem fil_step (T : LocLat G Qp LL O) (c : ZMod n) (τ : K →ₐ[Qp] LL)
    (hover : ∀ x : K₀, τ (algebraMap K₀ K x) = W.emb c x) (hsurj : Function.Surjective (algebraMap K₀ K))
    (a : ℤ) (hna : ¬ IsJumpV PD T.ρ τ a) {x : T.V ⊗[Qp] B} (hxD : x ∈ DcrisL PD T.ρ (W.emb c))
    (hx : x ∈ FilCris PD T.ρ a) : x ∈ FilCris PD T.ρ (a + 1) := by
  have hι : ιV PD (LL := LL) (V := T.V) x ∈ DdRE PD T.ρ τ :=
    Formalism.MainNotions.UnusedSlot80.LevR.ιDi_le W T c τ hover hsurj ⟨x, hxD, rfl⟩
  have h1 : ιV PD (LL := LL) (V := T.V) x ∈ FildR PD T.ρ τ a := ⟨hι, hx.2⟩
  have heq : FildR PD T.ρ τ (a + 1) = FildR PD T.ρ τ a := by
    by_contra hne; exact hna hne
  rw [← heq] at h1
  exact ⟨hx.1, h1.2⟩

theorem fil_low (T : LocLat G Qp LL O) (c : ZMod n) (τ : K →ₐ[Qp] LL)
    (hover : ∀ x : K₀, τ (algebraMap K₀ K x) = W.emb c x) (hsurj : Function.Surjective (algebraMap K₀ K))
    (H : ℕ) (hJ : ∀ a, IsJumpV PD T.ρ τ a → -(H : ℤ) ≤ a) {x : T.V ⊗[Qp] B}
    (hxD : x ∈ DcrisL PD T.ρ (W.emb c)) : x ∈ FilCris PD T.ρ (-(H : ℤ)) := by
  obtain ⟨u₀, hu₀⟩ := filV_exh (PD := PD) (LL := LL) (ιV PD (LL := LL) (V := T.V) x)
  have hx0 : x ∈ FilCris PD T.ρ u₀ := ⟨hxD.1, hu₀⟩
  by_cases hle : -(H : ℤ) ≤ u₀
  · exact Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti T.ρ hle hx0
  · have key : ∀ k : ℕ, u₀ + k ≤ -(H : ℤ) → x ∈ FilCris PD T.ρ (u₀ + k) := by
      intro k
      induction k with
      | zero => intro _; simpa using hx0
      | succ k ih =>
        intro hk
        have := fil_step W T c τ hover hsurj (u₀ + k) (fun hj => by have := hJ _ hj; push_cast at hk; omega)
          hxD (ih (by push_cast at hk; omega))
        push_cast; rwa [← add_assoc]
    have := key (-(H : ℤ) - u₀).toNat (by omega)
    rwa [show u₀ + ((-(H : ℤ) - u₀).toNat : ℤ) = -(H : ℤ) by omega] at this

theorem fil_high (T : LocLat G Qp LL O) (c : ZMod n) (τ : K →ₐ[Qp] LL)
    (hover : ∀ x : K₀, τ (algebraMap K₀ K x) = W.emb c x) (hsurj : Function.Surjective (algebraMap K₀ K))
    (H : ℕ) (hJ : ∀ a, IsJumpV PD T.ρ τ a → a ≤ (H : ℤ)) (u : ℤ) (hu : (H : ℤ) < u) {x : T.V ⊗[Qp] B}
    (hxD : x ∈ DcrisL PD T.ρ (W.emb c)) (hx : x ∈ FilCris PD T.ρ u) : x = 0 := by
  have key : ∀ k : ℕ, x ∈ FilCris PD T.ρ (u + k) := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      have := fil_step W T c τ hover hsurj (u + k) (fun hj => by have := hJ _ hj; omega) hxD ih
      push_cast; rwa [← add_assoc]
  have hall : ∀ a, ιV PD (LL := LL) (V := T.V) x ∈ FilV PD (LL := LL) (V := T.V) a := by
    intro a
    by_cases ha : a ≤ u
    · exact Formalism.MainNotions.UnusedSlot80.LevR.filV_anti ha hx.2
    · have := (key (a - u).toNat).2
      rwa [show u + ((a - u).toNat : ℤ) = a by omega] at this
  have h0 := filV_sep (PD := PD) _ hall
  exact Formalism.MainNotions.UnusedSlot80.LevR.ιV_inj (by rw [h0, map_zero])

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

theorem secIn_zero {a : ZMod n} {e d : ℕ} (cond : (ℕ → ℤ) → (Fin d → O) → Prop) :
    SecIn W a e cond (fun _ => 0) :=
  ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun k => by simp⟩

theorem secIn_add {a : ZMod n} {e d : ℕ} {cond : (ℕ → ℤ) → (Fin d → O) → Prop} {F F' : Fin d → W.EE}
    (h : SecIn W a e cond F) (h' : SecIn W a e cond F') : SecIn W a e cond (F + F') := by
  obtain ⟨I, g, c₀, α, hg, hF⟩ := h
  obtain ⟨I', g', c₀', α', hg', hF'⟩ := h'
  refine ⟨I + I', Fin.append g g', Fin.append c₀ c₀', Fin.append α α', fun i => ?_, fun k => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left]; exact hg i
    · simp only [Fin.append_right]; exact hg' i
  · rw [Pi.add_apply, hF k, hF' k, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]

theorem inFr_mulA {a : ZMod n} {num den : LetA O n} {f : W.EE} (h : InFr W a num den f) {c : LetA O n}
    (hc : c ∈ W.AΔ) : InFr W a num den (algebraMap (LetA O n) W.EE c * f) := by
  obtain ⟨u, hu, hf⟩ := h
  refine ⟨c * u, W.AΔ.mul_mem hc hu, ?_⟩
  rw [mul_left_comm, hf, ← map_mul]
  congr 1; ring

theorem inFr_add {a : ZMod n} {num den : LetA O n} {f f' : W.EE} (h : InFr W a num den f)
    (h' : InFr W a num den f') : InFr W a num den (f + f') := by
  obtain ⟨u, hu, hf⟩ := h
  obtain ⟨u', hu', hf'⟩ := h'
  refine ⟨u + u', W.AΔ.add_mem hu hu', ?_⟩
  rw [mul_add, hf, hf', ← map_add]
  congr 1; ring

theorem inFr_sub {a : ZMod n} {num den : LetA O n} {f f' : W.EE} (h : InFr W a num den f)
    (h' : InFr W a num den f') : InFr W a num den (f - f') := by
  obtain ⟨u, hu, hf⟩ := h
  obtain ⟨u', hu', hf'⟩ := h'
  refine ⟨u - u', W.AΔ.sub_mem hu hu', ?_⟩
  rw [mul_sub, hf, hf', ← map_sub]
  congr 1; ring

theorem inFr_zero {a : ZMod n} {num den : LetA O n} : InFr W a num den 0 :=
  ⟨0, W.AΔ.zero_mem, by simp⟩

theorem inFr_sum {a : ZMod n} {num den : LetA O n} {ι : Type} (s : Finset ι) (F : ι → W.EE)
    (h : ∀ j ∈ s, InFr W a num den (F j)) : InFr W a num den (∑ j ∈ s, F j) := by
  induction s using Finset.induction_on with
  | empty => simpa using inFr_zero W
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact inFr_add W (h j (Finset.mem_insert_self j s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem secIn_mulA {a : ZMod n} {e d : ℕ} {cond : (ℕ → ℤ) → (Fin d → O) → Prop} {F : Fin d → W.EE}
    (h : SecIn W a e cond F) {c : LetA O n} (hc : c ∈ W.AΔ) :
    SecIn W a e cond (fun k => algebraMap (LetA O n) W.EE c * F k) := by
  obtain ⟨I, g, c₀, α, hg, hF⟩ := h
  refine ⟨I, fun i => algebraMap (LetA O n) W.EE c * g i, c₀, α, fun i => ⟨inFr_mulA W (hg i).1 hc, (hg i).2⟩,
    fun k => ?_⟩
  show algebraMap (LetA O n) W.EE c * F k = _
  rw [hF k, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dvO_succ (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → O) :
    dvO W T (e + 1) b c₀ = Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V) (dvO W T e b c₀) := by
  unfold dvO dv
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, pow_succ', Module.End.mul_apply]

theorem dvO_add (T : LocLat G Qp LL O) (e s : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → O) :
    dvO W T (e + s) b c₀ = ((Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V)) ^ s) (dvO W T e b c₀) := by
  induction s with
  | zero => simp
  | succ s ih => rw [← add_assoc, dvO_succ, ih, pow_succ', Module.End.mul_apply]

theorem filS_succ (T : LocLat G Qp LL O) (a : ZMod n) (t : ℕ) (u : ℤ) :
    FilS W T (a + 1) (t + 1) u = (FilS W T a t u).map (Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V)) := by
  unfold FilS
  rw [show a + 1 - ((t + 1 : ℕ) : ZMod n) = a - (t : ZMod n) by push_cast; ring, ← Submodule.map_comp]
  congr 1
  rw [pow_succ', Module.End.mul_eq_comp]

variable [IsDomain O]

theorem secIn_transport (T : LocLat G Qp LL O) (a : ZMod n) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T)
    (H : ℕ) {v : LetA O n} (hv : v ∈ W.AΔ) (hπ : W.π₀ ∈ W.AΔ)
    (hlow : ∀ c₀ : Fin d → O, dvO W T (e + 1) b c₀ ∈ FilS W T (a + 1) 0 (-(H : ℤ))) (F : Fin d → W.EE)
    (hF : SecIn W a e (condNN W T a e b) F) :
    SecIn W (a + 1) (e + 1) (condNN W T (a + 1) (e + 1) b)
      (fun k => algebraMap (LetA O n) W.EE (ps W 0 ^ H * v) * W.φE (F k)) := by
  obtain ⟨I, g, c₀, α, hg, hFe⟩ := hF
  refine ⟨I, fun i => algebraMap (LetA O n) W.EE (ps W 0 ^ H * v) * W.φE (g i), c₀,
    fun i s => if s = 0 then (H : ℤ) else α i (s - 1), fun i => ⟨?_, ?_⟩, fun k => ?_⟩
  · obtain ⟨u, hu, hgu⟩ := (hg i).1
    refine ⟨v * W.φA u, W.AΔ.mul_mem hv (Formalism.MainNotions.UnusedSlot80.ToolsR.φ_AΔ hu), ?_⟩
    have hl : W.φA (letE a : LetA O n) = letE (a + 1) := by
      have := φA_letE W (a + 1); rwa [show a + 1 - 1 = a by ring] at this
    have h1 := congrArg W.φE hgu
    rw [map_mul, φE_alg, φE_alg, map_mul W.φA, map_mul W.φA, hl] at h1
    have hnum : W.φA (∏ s ∈ Finset.range e, ps W s ^ (α i s).toNat) =
        ∏ s ∈ Finset.range e, ps W (s + 1) ^ (α i s).toNat := by
      rw [map_prod]; exact Finset.prod_congr rfl fun s _ => by rw [map_pow, ← ps_succ]
    have hden : W.φA (∏ s ∈ Finset.range e, ps W s ^ (-(α i s)).toNat) =
        ∏ s ∈ Finset.range e, ps W (s + 1) ^ (-(α i s)).toNat := by
      rw [map_prod]; exact Finset.prod_congr rfl fun s _ => by rw [map_pow, ← ps_succ]
    rw [hnum, hden] at h1
    show algebraMap (LetA O n) W.EE (∏ s ∈ Finset.range (e + 1), ps W s ^
        (-(if s = 0 then (H : ℤ) else α i (s - 1))).toNat) *
        (algebraMap (LetA O n) W.EE (ps W 0 ^ H * v) * W.φE (g i)) =
      algebraMap (LetA O n) W.EE ((letE (a + 1) * ∏ s ∈ Finset.range (e + 1), ps W s ^
        (if s = 0 then (H : ℤ) else α i (s - 1)).toNat) * (v * W.φA u))
    rw [Finset.prod_range_succ', Finset.prod_range_succ']
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Int.toNat_natCast,
      Int.toNat_eq_zero.2 (by omega : -(H : ℤ) ≤ 0), pow_zero, mul_one]
    rw [mul_left_comm, h1]
    simp only [map_mul]
    ring
  · intro s hs
    rcases s with _ | t
    · beta_reduce
      simp only [↓reduceIte]
      exact hlow (c₀ i)
    · beta_reduce
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [filS_succ, dvO_succ]
      exact Submodule.mem_map_of_mem ((hg i).2 t (by omega))
  · show algebraMap (LetA O n) W.EE (ps W 0 ^ H * v) * W.φE (F k) = _
    rw [hFe k, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul W.φE, AlgHom.commutes]
    ring

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

theorem tau_over (hbij : Function.Bijective (algebraMap K₀ K)) (c : ZMod n) :
    ∃ τ : K →ₐ[Qp] LL, Formalism.MainNotions.LiftingTheory.Over W τ c ∧ ∀ x : K₀, τ (algebraMap K₀ K x) = W.emb c x := by
  let E : K₀ ≃ₐ[Qp] K := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hbij
  refine ⟨(W.emb c).comp E.symm.toAlgHom, ?_, fun x => ?_⟩
  · ext x
    simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
    congr 1
    exact E.symm_apply_apply x
  · simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
    congr 1
    exact E.symm_apply_apply x

theorem dvO_letter (T : LocLat G Qp LL O) (c' : ZMod n) {d : ℕ} (b : Fin d → W.DD T)
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (e : ℕ) (c₀ : Fin d → O) :
    dvO W T e b c₀ ∈ DcrisL PD T.ρ (W.emb (c' + (e : ZMod n))) := by
  unfold dvO dv
  refine Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ?_
  have hbN : b m ∈ W.N T := (hb.1 m).1.1
  have hbl : (letE c' : LetA O n) • b m = b m := Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T c' (hb.1 m).2
  have hcl : cmpD W T (b m) ∈ DcrisL PD T.ρ (W.emb c') := by
    rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hbN]; exact Formalism.MainNotions.UnusedSlot80.ArcF.cmp_mem_letter W T c' hbN hbl
  exact Formalism.MainNotions.UnusedSlot80.ArcF.φVB_pow_letter W T c' hcl e

variable [IsDomain O]

theorem dvO_filLow (hbij : Function.Bijective (algebraMap K₀ K)) (A : ArcP n) (hA : A.OK) (c' : ZMod n)
    (hc' : c' ∈ A.cuts) (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T)
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (e s : ℕ) (hse : s < e) (c₀ : Fin d → O) :
    dvO W T e b c₀ ∈ FilS W T (c' + (e : ZMod n)) s (-(A.Hs (c' + (e : ZMod n)) e s : ℤ)) := by
  set i : ZMod n := c' + ((e - s : ℕ) : ZMod n) with hidef
  obtain ⟨τ, hτ, hover⟩ := tau_over W hbij i
  have hJ : ∀ a, IsJumpV PD T.ρ τ a → -(A.Hs (c' + (e : ZMod n)) e s : ℤ) ≤ a := by
    intro a ha
    have hw := Formalism.MainNotions.UnusedSlot80.PhiPowers.win_sub A.G₀ A.S A.η (A.ty i) (hA.2.2.2.2.1 i) (hT.2 i τ hτ a ha)
    have hle := Formalism.MainNotions.UnusedSlot80.ArcC.hs_ge A hA c' hc' e (e - s) (by omega) (by omega)
    rw [show e - (e - s) = s by omega, ← hidef] at hle
    have := hw.1
    push_cast at this ⊢
    omega
  have hy := fil_low W T i τ hover hbij.2 _ hJ (dvO_letter W T c' b hb (e - s) c₀)
  refine ⟨dvO W T (e - s) b c₀, ⟨hy, ?_⟩, ?_⟩
  · rw [show c' + (e : ZMod n) - (s : ZMod n) = i by rw [hidef]; push_cast [Nat.cast_sub hse.le]; ring]
    exact dvO_letter W T c' b hb (e - s) c₀
  · rw [← dvO_add, Nat.sub_add_cancel hse.le]

theorem dvO_zero_high [NeZero n] (hbij : Function.Bijective (algebraMap K₀ K))
    (hinj : Function.Injective (algebraMap O LL)) (hV : Formalism.MainNotions.WachCoordinates.Br.ValRing (LL := LL) O v)
    (hs : W.s = 1) (h5 : ∀ (T : LocLat G Qp LL O) (M h : ZMod n → ℕ), IsCrys PD T.ρ →
      Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h → Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h)
    (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts) (T : LocLat G Qp LL O) (hT : Win W A T)
    (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) {d : ℕ} (b : Fin d → W.DD T)
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (e s : ℕ) (hse : s < e) (u : ℤ)
    (hu : (A.Hs (c' + (e : ZMod n)) e s : ℤ) < u) (c₀ : Fin d → O)
    (h : dvO W T e b c₀ ∈ FilS W T (c' + (e : ZMod n)) s u) : c₀ = 0 := by
  obtain ⟨y, ⟨hyF, hyD⟩, hye⟩ := h
  set i : ZMod n := c' + (e : ZMod n) - (s : ZMod n) with hidef
  obtain ⟨τ, hτ, hover⟩ := tau_over W hbij i
  have hHw : Hw A.G₀ A.S A.η (A.ty i) ≤ A.Hs (c' + (e : ZMod n)) e s :=
    Formalism.MainNotions.UnusedSlot80.ArcC.hw_le_hs A hA c' hc' e s hse
  have hJ : ∀ a, IsJumpV PD T.ρ τ a → a ≤ (Hw A.G₀ A.S A.η (A.ty i) : ℤ) := fun a ha =>
    (Formalism.MainNotions.UnusedSlot80.PhiPowers.win_sub A.G₀ A.S A.η (A.ty i) (hA.2.2.2.2.1 i) (hT.2 i τ hτ a ha)).2
  have hy0 := fil_high W T i τ hover hbij.2 _ hJ u (by omega) hyD hyF
  rw [hy0, map_zero] at hye
  have hfb := (Formalism.MainNotions.UnusedSlot80.ArcF.frame_basis W hs hV T h3 (h5 T _ _ hT.1 (jumpsLet_of_win W A hA T hT))
    hmod c' e b hb).1
  have hdv : dvO W T e b c₀ = ∑ m, algebraMap O LL (c₀ m) • dv W T e b (Pi.single m 1) := by
    simp only [Formalism.MainNotions.UnusedSlot80.ArcF.dv_single]; rfl
  have hsum : ∑ m, algebraMap O LL (c₀ m) • dv W T e b (Pi.single m 1) = 0 := by rw [← hdv, ← hye]
  funext m
  apply hinj
  rw [Fintype.linearIndependent_iff.1 hfb _ hsum m]
  simp

theorem secIn_piLam (hπ : W.π₀ ∈ W.AΔ) (A : ArcP n) (a : ZMod n) (e : ℕ) (T : LocLat G Qp LL O) {d : ℕ}
    (b : Fin d → W.DD T)
    (hlow : ∀ c₀ : Fin d → O, ∀ s < e, dvO W T e b c₀ ∈ FilS W T a s (-(A.Hs a e s : ℤ)))
    (h : Fin d → W.EE) (hh : ∀ k, InFr W a (W.π₀ * abelian₂ W A a e) 1 (h k)) :
    SecIn W a e (condNN W T a e b) h := by
  refine ⟨d, h, fun i => Pi.single i 1, fun _ s => (A.Hs a e s : ℤ), fun i => ⟨?_, ?_⟩, fun k => ?_⟩
  · obtain ⟨u, hu, hhu⟩ := hh i
    refine ⟨W.π₀ * u, W.AΔ.mul_mem hπ hu, ?_⟩
    have hnum : ∏ s ∈ Finset.range e, ps W s ^ ((A.Hs a e s : ℤ)).toNat = abelian₂ W A a e := by
      simp [abelian₂]
    have hden : ∏ s ∈ Finset.range e, ps W s ^ (-(A.Hs a e s : ℤ)).toNat = 1 :=
      Finset.prod_eq_one fun s _ => by rw [Int.toNat_eq_zero.2 (by omega), pow_zero]
    show algebraMap (LetA O n) W.EE (∏ s ∈ Finset.range e, ps W s ^ (-(A.Hs a e s : ℤ)).toNat) * h i =
      algebraMap (LetA O n) W.EE ((letE a * ∏ s ∈ Finset.range e, ps W s ^ ((A.Hs a e s : ℤ)).toNat) *
        (W.π₀ * u))
    rw [hden, hnum, ← one_mul (h i), ← map_one (algebraMap (LetA O n) W.EE), hhu, map_one, one_mul]
    congr 1; ring
  · intro s hs; exact hlow _ s hs
  · simp [Pi.single_apply]

end Formalism.MainNotions.UnusedSlot80.LevC
end
end
