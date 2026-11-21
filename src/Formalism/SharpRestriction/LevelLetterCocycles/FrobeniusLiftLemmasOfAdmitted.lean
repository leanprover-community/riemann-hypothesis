import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RhoLiftOf
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.FrobeniusSqBoundOfLocal
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ExistsXPowMul
import Formalism.SharpRestriction.LevelLetterCocycles.HermFlagUnipotentAnisotropicVectorSubMem
import Formalism.SharpRestriction.LevelLetterCocycles.LocalClauseOfFrobeniusHyps
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSeriesDeltaZero
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.JumpsLetExists
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.PtTransRec
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSZeroSplit
import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentMemInvariantsLetter
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowerCongruenceOfAdmitted
import Formalism.SharpRestriction.LevelLetterCocycles.CompleteMax
import Formalism.SharpRestriction.LevelLetterCocycles.UniformizerClauseOfAdmitted
import Formalism.SharpRestriction.LevelLetterCocycles.LocalClauseOfGammaLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.LemmaGsOfLemGAB
import Formalism.SharpRestriction.LevelLetterCocycles.RelayGeneralCaseOfAdmissible
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVNonneg
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IsExpSmulA
import Formalism.SharpRestriction.LevelLetterCocycles.UniversalGeneralOfRestriction
import Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorLevelsUnramifiedStatement
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ResiduePi0EqNegPrime
import Formalism.SharpRestriction.LevelLetterCocycles.UniformizerClauseOfAdmittedAlt

section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains

section LemGAla

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem lemGAla_φ_smul (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    W.φD T (a • x) = W.φA a • W.φD T x := by
  exact Formalism.MainNotions.LiftingTheory.wmap_φD_smul W T a x

theorem lemGAla_dl_smul (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) {i : ZMod n} {a : LetA O n}
    (ha : a ∈ W.AΔ) {x : W.DD T} (hx : Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x) : Formalism.MainNotions.CrystallineLiftingInputs.DL W T i (a • x) := by
  refine ⟨?_, fun δ hδ => ?_⟩
  · rw [smul_smul, mul_comm, ← smul_smul, hx.1]
  · rw [Formalism.MainNotions.LiftingTheory.wmap_γD_smul, ha δ hδ, hx.2 δ hδ]

theorem lemGAla_dl_φpow (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) {i : ZMod n} {x : W.DD T}
    (hx : Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x) (k : ℕ) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T (i + (k : ZMod n)) (((W.φD T) ^ k) x) := by
  have step : ∀ (j : ZMod n) (y : W.DD T), Formalism.MainNotions.CrystallineLiftingInputs.DL W T j y →
      Formalism.MainNotions.CrystallineLiftingInputs.DL W T (j + 1) (W.φD T y) := by
    intro j y hy
    refine ⟨?_, fun δ hδ => ?_⟩
    · have h := Formalism.MainNotions.LiftingTheory.wmap_φA_letE W (j + 1)
      rw [add_sub_cancel_right] at h
      rw [← h, ← Formalism.MainNotions.LiftingTheory.wmap_φD_smul, hy.1]
    · rw [← W.φγ_comm, hy.2 δ hδ]
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [Nat.cast_succ, ← add_assoc, pow_succ']
    exact step _ _ ih

theorem lemGAla_dl_trunc (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)
    (hO : ∀ c : O, ((PD.p : ℕ) : O) * c = 0 → c = 0) (hπ : W.π₀ ∈ W.AΔ) {c : ZMod n}
    {j M X σ : ℕ} {w z : W.DD T} (hw : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c w)
    (hz : Formalism.MainNotions.CrystallineLiftingInputs.IsTrunc W T c j M X σ w z) : Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c + (j : ZMod n)) z := by
  obtain ⟨cc, r, s, hser, hrem, rfl⟩ := hz
  have hzero : Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c + (j : ZMod n)) 0 := ⟨by simp, fun δ hδ => by simp⟩
  have hsub : ∀ a b : W.DD T, Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c + (j : ZMod n)) a →
      Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c + (j : ZMod n)) b → Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c + (j : ZMod n)) (a - b) :=
    fun a b ha hb => ⟨by rw [smul_sub, ha.1, hb.1], fun δ hδ => by rw [map_sub, ha.2 δ hδ, hb.2 δ hδ]⟩
  have hadd : ∀ a b : W.DD T, Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c + (j : ZMod n)) a →
      Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c + (j : ZMod n)) b → Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c + (j : ZMod n)) (a + b) :=
    fun a b ha hb => ⟨by rw [smul_add, ha.1, hb.1], fun δ hδ => by rw [map_add, ha.2 δ hδ, hb.2 δ hδ]⟩
  have hsmem : ∀ y, s y ∈ W.AΔ := by
    intro y
    obtain ⟨⟨⟨a, ha⟩, -⟩, hps⟩ := hrem y
    have hr : r y ∈ W.AΔ := by
      rw [ha]
      exact Subalgebra.sum_mem _ fun k _ =>
        Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Subalgebra.pow_mem _ hπ _)
    refine Formalism.MainNotions.UnusedSlot80.SatW.mem_AΔ_of_p_pow W hO (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y) ?_
    rw [hps]
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.natCast_mem _ _) _) hr
  have hw' : Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c + (j : ZMod n)) (((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) w) := by
    rw [← algebraMap_smul (LetA O n)]
    exact lemGAla_dl_smul W T (Subalgebra.algebraMap_mem _ _) (lemGAla_dl_φpow W T hw j)
  refine hsub _ _ hw' ?_
  exact Finset.sum_induction _ (Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c + (j : ZMod n))) hadd hzero
    (fun y _ => lemGAla_dl_smul W T (hsmem y) (lemGAla_dl_φpow W T (hser.2.1 y).1 j))

theorem pullback_level_two_to_one (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : ZMod n) (k : ℕ)
    (hπ : W.π₀ ∈ W.AΔ)
    (hgen : ∀ x, x ∈ W.N T → Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x →
      Formalism.MainNotions.LiftingTheory.qp W ^ k • W.φD T x ∈ W.N T) :
    ∀ p ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T c 2,
      Formalism.MainNotions.LiftingTheory.pk W 1 ^ k • p ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T (c + 1) 1 := by
  intro p hp
  have hqΔ : Formalism.MainNotions.LiftingTheory.qp W ∈ W.AΔ := W.AΔ.add_mem hπ (Subalgebra.natCast_mem _ _)
  unfold Formalism.MainNotions.CrystallineLiftingInputs.pullJ at hp ⊢
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, ⟨hyN, hyD⟩, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨Formalism.MainNotions.LiftingTheory.qp W ^ k • W.φD T y, ⟨hgen y hyN hyD, ?_⟩, ?_⟩
    · exact lemGAla_dl_smul W T (pow_mem hqΔ k) (by simpa using lemGAla_dl_φpow W T hyD 1)
    · simp only [pow_one, Formalism.MainNotions.LiftingTheory.pk]
      rw [Formalism.MainNotions.LiftingTheory.wmap_φD_smul, map_pow, pow_two]
      rfl
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [smul_smul, mul_comm, ← smul_smul]
    exact Submodule.smul_mem _ a hx

theorem lemGAla_pull1N (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : ZMod n) (k : ℕ)
    (hgen : ∀ x, x ∈ W.N T → Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x →
      Formalism.MainNotions.LiftingTheory.qp W ^ k • W.φD T x ∈ W.N T) :
    ∀ p ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T c 1, Formalism.MainNotions.LiftingTheory.qp W ^ k • p ∈ W.N T := by
  intro p hp
  unfold Formalism.MainNotions.CrystallineLiftingInputs.pullJ at hp
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, ⟨hyN, hyD⟩, rfl⟩ := hx
    simpa using hgen y hyN hyD
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [smul_smul, mul_comm, ← smul_smul]
    exact (W.N T).smul_mem a hx

theorem q_pow_smul_frobenius_mem' (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W)
    (hs : W.s = 1) {M h : ZMod n → ℕ} (h5 : Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h) (c : ZMod n) :
    ∀ x, x ∈ W.N T → Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x →
      Formalism.MainNotions.LiftingTheory.qp W ^ M (c + 1) • W.φD T x ∈ W.N T := by
  intro x hxN hxD
  have hxl : x ∈ W.Nl T c := by
    have h := Formalism.MainNotions.LiftingTheory.liftb_letE_mem W T c hxN
    rwa [hxD.1] at h
  have h := h5.1 (c + 1) x (by rwa [add_sub_cancel_right])
  exact (Formalism.MainNotions.LiftingTheory.lifta_Qq W hR hs T _ _).1 h

theorem lemGAla_parity {n : ℕ} [NeZero n] (hn : Even n) (d : ℕ) (i : ZMod n) (hi : (i.val + d) % 2 = 1) :
    ((i - 1).val + d) % 2 = 0 := by
  have h2 : 2 ∣ n := even_iff_two_dvd.1 hn
  have key : ∀ x : ZMod n, (((x.val : ℕ)) : ZMod 2) = ZMod.castHom h2 (ZMod 2) x := by
    intro x
    simp [ZMod.castHom_apply, ZMod.natCast_val]
  have h1 : (((i.val + d : ℕ)) : ZMod 2) = 1 := by
    rw [← ZMod.natCast_mod, hi]
    rfl
  rw [← Nat.dvd_iff_mod_eq_zero, ← CharP.cast_eq_zero_iff (ZMod 2) 2]
  push_cast at h1 ⊢
  rw [key (i - 1), map_sub, map_one, ← key i]
  linear_combination h1

theorem lemGA_la_of [NeZero n] (W : LocWach PD LL O v n) (hT2 : Formalism.MainNotions.CrystallineLiftingInputs.TTool2 W)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W)
    (hJ : ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
      SetCS W d T₁ T₂ F b S η m → Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T₂ (MiW d b S η) (hiW d b S η)) :
    LemGA_la W := by
  intro d T₁ T₂ F b S η m hset i hi y hyN hyD
  have hsetc := hset
  obtain ⟨hA, hp11, hn, ⟨hdom, -, -⟩, ⟨ζ, hζ⟩, hsur, -, -, hbig, -⟩ := hset
  haveI := hdom
  have hs : W.s = 1 := hA.2.1
  have hc2 : IsCrys PD T₂.ρ := hsur.2.1
  have hO : ∀ c : O, ((PD.p : ℕ) : O) * c = 0 → c = 0 := by
    intro c hc
    haveI : NeZero PD.p := ⟨by omega⟩
    have hpL : ((PD.p : ℕ) : LL) ≠ 0 := hζ.neZero'.out
    have hpO : ((PD.p : ℕ) : O) ≠ 0 := fun h =>
      hpL (by rw [← map_natCast (algebraMap O LL), h, map_zero])
    exact (mul_eq_zero.1 hc).resolve_left hpO
  have hfin : finrank K₀ K = 1 := by
    have e := LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hA.1
    rw [← e.finrank_eq, finrank_self]
  obtain ⟨-, -, h9f⟩ := h9 T₂ hc2 hs hA.2.2
  obtain ⟨-, hmod⟩ := h9f hfin
  obtain ⟨-, hγN⟩ := hmod
  have hyΔ : y ∈ W.NΔ T₂ := ⟨hyN, hyD.2⟩
  obtain ⟨y', hy'Δ, hy'⟩ := hγN y hyΔ
  have hInI : Formalism.MainNotions.CrystallineLiftingInputs.InI W T₂ (i - 2) y := by
    refine ⟨hyD, ⟨0, ?_⟩, ⟨y', hy'Δ.1, hy'Δ.2, by rw [pow_one]; exact hy'⟩⟩
    first
      | exact hyN
      | (simp only [LocWach.InvN]; simpa using hyN)
      | (unfold LocWach.InvN; simpa [Formalism.MainNotions.DeltaInvariantLattices.invN, Formalism.MainNotions.DeltaInvariantLattices.smulA] using hyN)
  have hqΔ : Formalism.MainNotions.LiftingTheory.qp W ∈ W.AΔ := W.AΔ.add_mem hR.πΔ (Subalgebra.natCast_mem _ _)
  set H := hpar n b S + η with hH
  obtain ⟨hex, hcl, -⟩ := (hT2 hA hp11 2 1 (2 * H) (lemG_sig PD.p H) (Or.inr ⟨rfl, rfl, rfl⟩)).1
    T₂ hc2 (i - 2)
  obtain ⟨la, hla⟩ := hex y hInI
  obtain ⟨hdiff, p0, hp0, hγla⟩ := hcl y la hInI hla
  have h5T := h5 T₂ _ _ hc2 (hJ d T₁ T₂ F b S η m hsetc)
  have hpar1 : ((i - 1).val + d) % 2 = 0 := lemGAla_parity hn d i hi
  have hM1 : MiW d b S η (i - 1) = b (i - 1) + S := by simp [MiW, hpar1]
  have hMi : MiW d b S η i = η := by simp [MiW, hi]
  have hgen1 : ∀ x, x ∈ W.N T₂ → Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ (i - 2) x →
      Formalism.MainNotions.LiftingTheory.qp W ^ (b (i - 1) + S) • W.φD T₂ x ∈ W.N T₂ := by
    intro x hx hxD
    have h := q_pow_smul_frobenius_mem' W T₂ hR hs h5T (i - 2) x hx hxD
    rwa [show i - 2 + 1 = i - 1 by ring, hM1] at h
  have hgen2 : ∀ x, x ∈ W.N T₂ → Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ (i - 1) x →
      Formalism.MainNotions.LiftingTheory.qp W ^ η • W.φD T₂ x ∈ W.N T₂ := by
    intro x hx hxD
    have h := q_pow_smul_frobenius_mem' W T₂ hR hs h5T (i - 1) x hx hxD
    rwa [sub_add_cancel, hMi] at h
  have hla_mem : la ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T₂ (i - 2) 2 := by
    have hgenp : ((PD.p : ℕ) : O) ^ lemG_sig PD.p H • ((W.φD T₂) ^ 2) y ∈
        Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T₂ (i - 2) 2 := by
      rw [← algebraMap_smul (LetA O n)]
      refine Submodule.smul_mem _ _ ?_
      unfold Formalism.MainNotions.CrystallineLiftingInputs.pullJ
      exact Submodule.subset_span ⟨y, ⟨hyN, hyD⟩, rfl⟩
    have h := Submodule.add_mem _ hdiff hgenp
    rwa [sub_add_cancel] at h
  have hpull : Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • la ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T₂ (i - 1) 1 := by
    have h := pullback_level_two_to_one W T₂ (i - 2) (b (i - 1) + S) hR.πΔ hgen1 la hla_mem
    rwa [show i - 2 + 1 = i - 1 by ring] at h
  have hDLi : Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ i la := by
    have h := lemGAla_dl_trunc W T₂ hO hR.πΔ hyD hla
    simpa using h
  have hp0' : Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • p0 ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T₂ (i - 1) 1 := by
    have h := pullback_level_two_to_one W T₂ (i - 2) (b (i - 1) + S) hR.πΔ hgen1 p0 hp0
    rwa [show i - 2 + 1 = i - 1 by ring] at h
  have hN1 := lemGAla_pull1N W T₂ (i - 1) η hgen2 _ hp0'

  have hle : ⌈aR PD.p H⌉₊ + b i + η ≤ 2 * H := by
    have hbi : b i ≤ hpar n b S :=
      le_trans (Finset.le_sup (f := b) (Finset.mem_univ i)) (Nat.le_add_right _ _)
    have hb := hbig i
    rcases le_or_gt 0 (aR PD.p H) with h0 | h0
    · have hc := Nat.ceil_lt_add_one h0
      have hbi' : (b i : ℝ) ≤ (hpar n b S : ℝ) := by exact_mod_cast hbi
      have hreal : ((⌈aR PD.p H⌉₊ : ℕ) : ℝ) + (b i : ℝ) + (η : ℝ) ≤ 2 * ((hpar n b S : ℝ) + η) := by
        linarith
      rw [hH]
      exact_mod_cast hreal
    · have hc : ⌈aR PD.p H⌉₊ = 0 := Nat.ceil_eq_zero.2 h0.le
      rw [hc, hH]
      omega
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hle
  set a := W.π₀ * Formalism.MainNotions.LiftingTheory.qp W ^ (⌈aR PD.p H⌉₊ + b i) with ha_def
  have haΔ : a ∈ W.AΔ := W.AΔ.mul_mem hR.πΔ (W.AΔ.pow_mem hqΔ _)
  have hpkΔ : Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) ∈ W.AΔ :=
    W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.PhiPowers.φA_pow_mem_AΔ (W := W) hqΔ 1) _
  have hcancel : ∀ x x' : W.DD T₂, a • x = a • x' → x = x' := by
    intro x x' h
    rw [ha_def, mul_comm, ← smul_smul, ← smul_smul] at h
    have h1 := (Formalism.MainNotions.LiftingTheory.lifta_qpow_bij W hR T₂ _).1 h
    obtain ⟨u, hu⟩ := hR.πU
    exact Formalism.MainNotions.LiftingTheory.lifta_π₀_cancel W T₂ (↑u⁻¹ : W.EE) (by rw [← hu]; exact u.mul_inv) x x' h1
  set w := Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • (W.γ T₂ la - la) with hw_def
  have hγDL : Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ i (W.γ T₂ la) := by
    refine ⟨?_, fun δ hδ => ?_⟩
    · conv_lhs => rw [← Formalism.MainNotions.WachCoordinates.Br.γA_letE W W.gam i]
      rw [← Formalism.MainNotions.LiftingTheory.liftb_γ_smul, hDLi.1]
    · show W.γD T₂ δ (W.γD T₂ W.gam la) = W.γD T₂ W.gam la
      rw [← W.γD_mul, mul_comm, W.γD_mul, hDLi.2 δ hδ]
  have hwDL : Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ i w := by
    refine lemGAla_dl_smul W T₂ hpkΔ ⟨?_, fun δ hδ => ?_⟩
    · rw [smul_sub, hγDL.1, hDLi.1]
    · rw [map_sub, hγDL.2 δ hδ, hDLi.2 δ hδ]
  set z := Formalism.MainNotions.LiftingTheory.qp W ^ t • (Formalism.MainNotions.LiftingTheory.qp W ^ η • (Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • p0))
    with hz_def
  have hzN : z ∈ W.N T₂ := Submodule.smul_mem _ _ hN1
  have hz_eq : a • z = w := by
    rw [hw_def, hγla, hz_def, ha_def, Formalism.MainNotions.CrystallineLiftingInputs.fMX, ht]
    simp only [smul_smul]
    congr 1
    ring
  refine ⟨la, hla, hDLi, hpull, z, hzN, ⟨hcancel _ _ ?_, fun δ hδ => hcancel _ _ ?_⟩, ?_⟩
  · rw [smul_smul, mul_comm, ← smul_smul, hz_eq, hwDL.1]
  · calc a • W.γD T₂ δ z = W.γA δ a • W.γD T₂ δ z := by rw [haΔ δ hδ]
      _ = W.γD T₂ δ (a • z) := (Formalism.MainNotions.LiftingTheory.wmap_γD_smul W T₂ δ a z).symm
      _ = a • z := by rw [hz_eq, hwDL.2 δ hδ]
  · rw [← hw_def, ← hz_eq]

end LemGAla

end Formalism.MainNotions.RamifiedCoefficientChains.S9
end
end

section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains

section JumpsT2

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem jumps_in_letter_of_crystalline [NeZero n] (W : LocWach PD LL O v n) (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL)
    (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) :
    ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
      SetCS W d T₁ T₂ F b S η m → Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T₂ (MiW d b S η) (hiW d b S η) :=
  fun _ _ _ _ _ _ _ _ hS => Formalism.MainNotions.N.Pv.LocalLengthBound.rk_jumpsLet₂ W hE hC hQ hS

theorem liftRing_of_uniformizer_clause (W : LocWach PD LL O v n) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) :
    Formalism.MainNotions.LiftingTheory.lifta_Ring W :=
  Formalism.MainNotions.LiftingTheory.lifta_ring_of W (Formalism.MainNotions.LiftingTheory.uniformizer_ring_and_module_clauses W h9 hA T hT).1

theorem lemGA_la_of_adm [NeZero n] (W : LocWach PD LL O v n) (hT2 : Formalism.MainNotions.CrystallineLiftingInputs.TTool2 W)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL)
    (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) : LemGA_la W := by
  intro d T₁ T₂ F b S η m hS
  exact lemGA_la_of W hT2 h9 h5
    (liftRing_of_uniformizer_clause W h9 hS.1 T₂ hS.2.2.2.2.2.1.2.1) (jumps_in_letter_of_crystalline W hE hC hQ)
    d T₁ T₂ F b S η m hS

end JumpsT2

end Formalism.MainNotions.RamifiedCoefficientChains.S9
end
end

section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains
open Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section LemGAxF

variable {R M : Type} [Field R] [AddCommGroup M] [Module R M]

def lemGAx_F (B K : ℤ) (c : M) (k : ℤ) : Submodule R M :=
  if k < -B then ⊥ else if k < K then Submodule.span R {c} else ⊤

theorem lemGAx_F_mono (B K : ℤ) (c : M) : Monotone (lemGAx_F (R := R) B K c) := by
  intro a a' h
  unfold lemGAx_F
  split_ifs <;> first | exact bot_le | exact le_top | exact le_rfl | (exfalso; omega)

end LemGAxF

section LemGAx

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem lemGAx_pull1N (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : ZMod n) (k : ℕ)
    (hgen : ∀ x, x ∈ W.N T → Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x →
      Formalism.MainNotions.LiftingTheory.qp W ^ k • W.φD T x ∈ W.N T) :
    ∀ p ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T c 1, Formalism.MainNotions.LiftingTheory.qp W ^ k • p ∈ W.N T := by
  intro p hp
  induction hp using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨x, ⟨hxN, hxD⟩, rfl⟩ := hg
    simpa using hgen x hxN hxD
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx

theorem q_pow_smul_frobenius_mem (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W)
    (hs : W.s = 1) {M h : ZMod n → ℕ} (h5 : Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h) (c : ZMod n) :
    ∀ x, x ∈ W.N T → Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x →
      Formalism.MainNotions.LiftingTheory.qp W ^ M (c + 1) • W.φD T x ∈ W.N T := by
  intro x hxN hxD
  have hxl : x ∈ W.Nl T (c + 1 - 1) := by
    rw [add_sub_cancel_right]
    exact ⟨x, hxN, by rw [LinearMap.smul_apply, LinearMap.id_apply, hxD.1]⟩
  exact (Formalism.MainNotions.LiftingTheory.lifta_Qq W hR hs T _ _).1 (h5.1 (c + 1) x hxl)

theorem lemGAx_parity {n : ℕ} [NeZero n] (hn : Even n) (d : ℕ) (i : ZMod n) (hi : (i.val + d) % 2 = 1) :
    ((i - 1).val + d) % 2 = 0 := by
  have := parity_succ hn d (i - 1)
  rw [sub_add_cancel] at this
  omega

theorem lemGA_x_of [NeZero n] (W : LocWach PD LL O v n)
    (hER : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRing W) (hEU : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules W)
    (hEC : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit W) (hTH : Formalism.MainNotions.CrystallineLiftingInputs.THor W)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W)
    (hJ : ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
      SetCS W d T₁ T₂ F b S η m → Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T₂ (MiW d b S η) (hiW d b S η)) :
    GammaActionLemma W := by
  intro d T₁ T₂ F b S η m hS i hi y hy hyD hFil la hla
  obtain ⟨htr, hlaD, hlaP, -⟩ := hla
  have hA : Formalism.MainNotions.LiftingTheory.CaseA W := hS.1
  have hl : 11 ≤ PD.p := hS.2.1
  have hn : Even n := hS.2.2.1
  have hT : IsCrys PD T₂.ρ := hS.2.2.2.2.2.1.2.1
  have hπ : W.π₀ ∈ W.AΔ := hR.πΔ
  have hq : Formalism.MainNotions.LiftingTheory.qp W ∈ W.AΔ := W.AΔ.add_mem hπ (W.AΔ.natCast_mem _)
  have hp1 : Formalism.MainNotions.LiftingTheory.pk W 1 ∈ W.AΔ := Formalism.MainNotions.UnusedSlot80.Relay2.pk_mem_AΔ W hπ 1
  have hJ2 := hJ d T₁ T₂ F b S η m hS
  have hp5 := h5 T₂ (MiW d b S η) (hiW d b S η) hT hJ2
  have hpar1 := lemGAx_parity hn d i hi
  have hMi : MiW d b S η i = η := by unfold MiW; rw [if_neg (by omega)]
  have hM2 : MiW d b S η (i - 1 + 1) = η := by rw [sub_add_cancel]; exact hMi
  have hbH : b i ≤ hpar n b S := by
    unfold hpar; exact le_trans (Finset.le_sup (Finset.mem_univ i)) (Nat.le_add_right _ _)
  set H := hpar n b S + η with hH
  set σ := lemG_sig PD.p H with hσ
  set h₂ := b (i - 1) + S with hh₂

  have hg2 : ∀ x, x ∈ W.N T₂ → Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ (i - 1) x →
      Formalism.MainNotions.LiftingTheory.qp W ^ η • W.φD T₂ x ∈ W.N T₂ := by
    intro x hxN hxD
    have := q_pow_smul_frobenius_mem W T₂ hR hA.2.1 hp5 (i - 1) x hxN hxD
    rwa [hM2] at this
  have hm0 : Formalism.MainNotions.LiftingTheory.qp W ^ η • (Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂ • la) ∈ W.N T₂ :=
    lemGAx_pull1N W T₂ (i - 1) η hg2 _ hlaP

  obtain ⟨Uq, hUq⟩ := hR.qU
  set x : W.DD T₂ := ((Uq⁻¹ : W.EEˣ) : W.EE) ^ b i • (Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂ • la) with hxdef
  have hxe : Formalism.MainNotions.LiftingTheory.qp W ^ b i • x = Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂ • la := by
    rw [hxdef, ← algebraMap_smul W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ b i), smul_smul, map_pow, ← hUq, ← mul_pow,
      Units.mul_inv, one_pow, one_smul]
  have hqU : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ b i)) := by
    rw [map_pow]; exact hR.qU.pow _
  have hxD : Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ i x := by
    refine ⟨?_, fun δ hδ => ?_⟩
    · apply Formalism.MainNotions.UnusedSlot80.SatW.smul_cancel W T₂ hqU
      rw [smul_comm, hxe, smul_comm, hlaD.1]
    · apply Formalism.MainNotions.UnusedSlot80.SatW.smul_cancel W T₂ hqU
      calc Formalism.MainNotions.LiftingTheory.qp W ^ b i • W.γD T₂ δ x
          = W.γA δ (Formalism.MainNotions.LiftingTheory.qp W ^ b i) • W.γD T₂ δ x := by rw [(W.AΔ.pow_mem hq (b i)) δ hδ]
        _ = W.γD T₂ δ (Formalism.MainNotions.LiftingTheory.qp W ^ b i • x) :=
            (Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA' W T₂ δ _ x).symm
        _ = W.γD T₂ δ (Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂ • la) := by rw [hxe]
        _ = W.γA δ (Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂) • W.γD T₂ δ la :=
            Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA' W T₂ δ _ la
        _ = Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂ • la := by rw [(W.AΔ.pow_mem hp1 h₂) δ hδ, hlaD.2 δ hδ]
        _ = Formalism.MainNotions.LiftingTheory.qp W ^ b i • x := hxe.symm
  have hmx : Formalism.MainNotions.LiftingTheory.qp W ^ (b i + η) • x ∈ W.N T₂ := by
    rw [pow_add, mul_comm, mul_smul, hxe]; exact hm0

  obtain ⟨ζ, hζ⟩ := hS.2.2.2.2.1
  obtain ⟨⟨u, hu, hlq⟩, -, -⟩ := hER hA i ζ hζ
  have hu0 : PowerSeries.constantCoeff u ≠ 0 := (PowerSeries.isUnit_iff_constantCoeff.1 hu).ne_zero
  have hlevq : W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ (b i + η)) =
      PowerSeries.X ^ (b i + η) * u ^ (b i + η) := by
    rw [map_pow, hlq, mul_pow, mul_comm]
  have hlev0 : W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ (b i + η)) ≠ 0 := by
    rw [hlevq]
    exact mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) (pow_ne_zero _ hu.ne_zero)
  obtain ⟨dx, hdx, -⟩ := (hEU hA T₂ hT i ζ hζ).1 x _ hmx hlev0
  obtain ⟨m₀, hm₀⟩ := hdx.1
  have hLB : LB m₀ dx := hm₀
  have hrel : W.levN T₂ i ζ ⟨_, hmx⟩ = fun k => smulS (u ^ (b i + η)) dx (k - ((b i + η : ℕ) : ℤ)) := by
    have h1 := Formalism.MainNotions.N.Pv.LocalLengthBound.isExp_smulA W T₂ i ζ hdx (Formalism.MainNotions.LiftingTheory.qp W ^ (b i + η))
    have h2 := Formalism.MainNotions.N.Pv.LocalLengthBound.isExp_self W T₂ i ζ hmx
    rw [Formalism.MainNotions.N.Pv.LocalLengthBound.isExp_unique W T₂ i ζ h2 h1, hlevq, smulS_mul hLB,
      smulS_X_pow (LB_smulS hLB _)]
  have hsh : ∀ k : ℤ, smulS (u ^ (b i + η)) dx k =
      W.levN T₂ i ζ ⟨_, hmx⟩ (k + ((b i + η : ℕ) : ℤ)) := by
    intro k; rw [hrel]; simp

  have hyΔ : Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (i - 2) y :=
    Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_of W T₂ (i - 2) ⟨hy, hyD.2⟩ hyD.1
  have hyI : Formalism.MainNotions.CrystallineLiftingInputs.InI W T₂ (i - 2) y := by
    refine ⟨hyD, ⟨0, 0, by simpa using hy⟩, ?_⟩
    obtain ⟨x', hx', he⟩ := Formalism.MainNotions.LiftingTheory.coreH_graded_of W h9 hA T₂ hT (i - 2) 0 y hyΔ
    refine ⟨x', hx'.1.1, hx'.1.2, ?_⟩
    simpa using he
  have hTC : Formalism.MainNotions.CrystallineLiftingInputs.TCase PD.p 2 1 (2 * H) σ := Or.inr ⟨rfl, rfl, rfl⟩
  have hk : (Formalism.MainNotions.LiftingTheory.qp W ^ η * Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂) • la ∈ W.N T₂ := by
    rw [mul_smul]; exact hm0
  have hmm : (⟨Formalism.MainNotions.LiftingTheory.qp W ^ (b i + η) • x, hmx⟩ : ↥(W.N T₂)) = ⟨_, hk⟩ := by
    apply Subtype.ext
    show Formalism.MainNotions.LiftingTheory.qp W ^ (b i + η) • x = (Formalism.MainNotions.LiftingTheory.qp W ^ η * Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂) • la
    rw [pow_add, mul_comm (Formalism.MainNotions.LiftingTheory.qp W ^ b i), mul_smul, hxe, mul_smul]
  obtain ⟨hneg, hcoef⟩ := hTH hA hl 2 1 (2 * H) σ hTC T₂ hT (i - 2) y la hy hyI htr ζ (η + 2 * H) η
    (Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂) hk (Or.inl ⟨hζ, rfl⟩)
  have e2 : i - 2 + ((2 : ℕ) : ZMod n) = i := by push_cast; ring
  rw [e2] at hneg hcoef
  set c0 : TensorProduct Qp T₂.V BdR := (PD.p : LL) ^ σ • ιV PD (LL := LL) (V := T₂.V)
    ((φVB PD (LL := LL) (V := T₂.V))^[2] (W.cmp T₂ ⟨y, hy⟩)) with hc0
  have hlevk : W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ η * Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂) =
      PowerSeries.X ^ η * (u ^ η * W.lev i ζ (Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂)) := by
    rw [map_mul, map_pow (W.lev i ζ) (Formalism.MainNotions.LiftingTheory.qp W) η, hlq, mul_pow, mul_comm (u ^ η), mul_assoc]
  have hc00 : ∀ r : ℕ, r < η →
      PowerSeries.coeff r (W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ η * Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂)) = 0 := by
    intro r hr
    rw [hlevk, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

  have hg : ∀ k : ℤ, smulS (u ^ (b i + η)) dx k ∈
      lemGAx_F (R := LL) (b i : ℤ) (((2 * H : ℕ) : ℤ) - (b i : ℤ)) c0 k := by
    intro k
    rw [hsh, hmm]
    unfold lemGAx_F
    by_cases hk0 : k + ((b i + η : ℕ) : ℤ) < 0
    · rw [hneg _ hk0]
      split_ifs <;> exact Submodule.zero_mem _
    · obtain ⟨r, hr⟩ : ∃ r : ℕ, k + ((b i + η : ℕ) : ℤ) = r :=
        ⟨(k + ((b i + η : ℕ) : ℤ)).toNat, by omega⟩
      rw [hr]
      push_cast at hr
      split_ifs with h1 h2
      · rw [hcoef r (by omega), hc00 r (by omega), zero_smul]
        exact Submodule.zero_mem _
      · rw [hcoef r (by push_cast at h2; omega)]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      · trivial
  have hF := Formalism.MainNotions.UnusedSlot80.LevR.laurent_div (lemGAx_F (R := LL) (b i : ℤ) (((2 * H : ℕ) : ℤ) - (b i : ℤ)) c0)
    (lemGAx_F_mono _ _ _) hm₀ (u ^ (b i + η)) (by rw [map_pow]; exact pow_ne_zero _ hu0) hg

  have hcy : W.cmp T₂ ⟨y, hy⟩ ∈ DcrisL PD T₂.ρ (W.emb (i - 2)) := by
    have h := W.cmp_letter T₂ (i - 2) ⟨y, hy⟩
    have e : ((letE (i - 2) : LetA O n) • (⟨y, hy⟩ : ↥(W.N T₂))) = ⟨y, hy⟩ := Subtype.ext hyD.1
    rwa [e] at h
  have hφy : (φVB PD (LL := LL) (V := T₂.V))^[2] (W.cmp T₂ ⟨y, hy⟩) ∈ DcrisL PD T₂.ρ (W.emb i) := by
    have h := Formalism.MainNotions.UnusedSlot80.UnivC.φVB_pow_letter W T₂ (i - 2) 2 hcy
    rwa [e2, Module.End.pow_apply] at h
  have hc0mem : ∀ k : ℤ, -(b i : ℤ) ≤ k →
      c0 ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T₂ i ⊓ FilV PD (LL := LL) (V := T₂.V) (-k) := by
    intro k hk
    refine Submodule.mem_inf.2 ⟨Submodule.smul_mem _ _ ⟨_, hφy, rfl⟩, Submodule.smul_mem _ _ ?_⟩
    have hF0 : ιV PD (LL := LL) (V := T₂.V)
        ((φVB PD (LL := LL) (V := T₂.V))^[2] (W.cmp T₂ ⟨y, hy⟩)) ∈
          FilV PD (LL := LL) (V := T₂.V) (b i : ℤ) := (Submodule.mem_inf.1 hFil).2
    exact Formalism.MainNotions.UnusedSlot80.LevR.filV_anti (PD := PD) (show -k ≤ (b i : ℤ) by omega) hF0
  set τ := Formalism.MainNotions.N.Pv.LocalLengthBound.tauOf W hA.1 i with hτ
  have hover : Formalism.MainNotions.DeltaInvariantLattices.OverLetter W τ i := by
    apply AlgHom.ext
    intro c
    rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
    exact Formalism.MainNotions.N.Pv.LocalLengthBound.tauOf_over W hA.1 i c
  have hjump : ∀ a, IsJumpV PD T₂.ρ τ a → -(η : ℤ) ≤ a := by
    intro a ha
    have := (hJ2 τ i hover a ha).1
    rwa [hMi] at this
  have hDi : Formalism.MainNotions.DeltaInvariantLattices.ιDi W T₂ i ≤ FilV PD (LL := LL) (V := T₂.V) (-(η : ℤ)) := by
    intro z hz
    have h1 := Formalism.MainNotions.UnusedSlot80.LevR.ιDi_le W T₂ i τ (Formalism.MainNotions.N.Pv.LocalLengthBound.tauOf_over W hA.1 i) hA.1.2 hz
    rw [← Formalism.MainNotions.UnusedSlot80.UnivF.fildR_eq_top_of (PD := PD) (ρ := T₂.ρ) τ (-(η : ℤ)) hjump] at h1
    exact (Submodule.mem_inf.1 h1).2

  have hxN : x ∈ W.N T₂ := by
    refine ((hEC hA T₂ hT i ζ hζ x dx hxD hdx).1 ⟨b i + η, hmx⟩).2 fun k => ?_
    have hk := hF k
    rw [Formalism.MainNotions.UnusedSlot80.LevR.filLev_zero W T₂ i (-k)]
    unfold lemGAx_F at hk
    split_ifs at hk with h1 h2
    · rw [(Submodule.mem_bot LL).1 hk]; exact Submodule.zero_mem _
    · exact (Submodule.span_le.2 (Set.singleton_subset_iff.2 (hc0mem k (by omega)))) hk
    · refine Submodule.mem_inf.2 ⟨(hEU hA T₂ hT i ζ hζ).2.1 x dx hxD hdx k, ?_⟩
      refine Formalism.MainNotions.UnusedSlot80.LevR.filV_anti (PD := PD) (show -k ≤ -(η : ℤ) by push_cast at h2; omega)
        (hDi ((hEU hA T₂ hT i ζ hζ).2.1 x dx hxD hdx k))
  exact ⟨x, hxN, hxD, hxe⟩

end LemGAx

end Formalism.MainNotions.RamifiedCoefficientChains.S9
end
end

section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

section LemGA0

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem lemGA0_ιV_inj (T : LocLat G Qp LL O) : Function.Injective (ιV PD (LL := LL) (V := T.V)) :=
  Module.Flat.lTensor_preserves_injective_linearMap (R := Qp) (M := T.V)
    (PD.ι.toLinearMap.restrictScalars Qp) PD.ι_inj

theorem lemGA0_one_root (l : ℕ) : ∃ j : ℕ, IsPrimitiveRoot (1 : LL) (l ^ j) := ⟨0, by simpa using IsPrimitiveRoot.one⟩

theorem lemGA0_cc_letπ (W : LocWach PD LL O v n) (i : ZMod n) :
    PowerSeries.constantCoeff (W.lev i 1 (letπ : LetA O n)) = 0 := by
  obtain ⟨E, hE0, -, hE⟩ := W.lev_π i 1 (lemGA0_one_root PD.p)
  have h := congrArg PowerSeries.constantCoeff hE
  simp only [map_add, map_one, hE0, one_mul] at h
  linear_combination h

theorem lemGA0_cc_π₀₁ (W : LocWach PD LL O v n) (hcard : W.DelF.card = PD.p - 1) (hp : 1 ≤ PD.p) :
    PowerSeries.constantCoeff W.π₀₁ = 0 := by
  unfold LocWach.π₀₁
  have h2 : ∀ δ, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = (0 : O) := fun δ => (W.γ₀_X δ).1
  simp only [map_add, map_sub, map_one, map_natCast, map_sum, h2, add_zero, Finset.sum_const,
    nsmul_eq_mul, mul_one, hcard]
  push_cast [Nat.cast_sub hp]
  ring

theorem lemGA0_cc_π₀ (W : LocWach PD LL O v n) (i : ZMod n) (h0 : PowerSeries.constantCoeff W.π₀₁ = 0) :
    PowerSeries.constantCoeff (W.lev i 1 W.π₀) = 0 := by
  obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.mpr h0
  have e : W.π₀ = (letπ : LetA O n) * (fun _ => g) := by
    funext j
    show W.π₀₁ = PowerSeries.X * g
    exact hg
  rw [e, map_mul, map_mul, lemGA0_cc_letπ, zero_mul]

theorem lemGA0_cc_qp (W : LocWach PD LL O v n) (i : ZMod n) (h0 : PowerSeries.constantCoeff W.π₀₁ = 0) :
    PowerSeries.constantCoeff (W.lev i 1 (Formalism.MainNotions.LiftingTheory.qp W)) = (PD.p : LL) := by
  unfold Formalism.MainNotions.LiftingTheory.qp
  rw [map_add, map_natCast, map_add, lemGA0_cc_π₀ W i h0, map_natCast, zero_add]

variable {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]

theorem lemGA0_cc_pk (W : LocWach PD LL O v n) {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (C : CmpTie W E ιdR p1 tS zS) (i : ZMod n) (h0 : PowerSeries.constantCoeff W.π₀₁ = 0) :
    PowerSeries.constantCoeff (W.lev i 1 (Formalism.MainNotions.LiftingTheory.pk W 1)) = (PD.p : LL) := by
  have e : Formalism.MainNotions.LiftingTheory.pk W 1 = W.φA (Formalism.MainNotions.LiftingTheory.qp W) := by
    unfold Formalism.MainNotions.LiftingTheory.pk; rw [pow_one]
  rw [e, C.lev_φ i 1 (lemGA0_one_root PD.p) (Formalism.MainNotions.LiftingTheory.qp W), one_pow,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, one_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, lemGA0_cc_qp W (i - 1) h0]

theorem lemGA0_conv_vanish {M : Type} [AddCommGroup M] [Module LL M] (f : PowerSeries LL) (d : ℤ → M)
    (hf : PowerSeries.constantCoeff f ≠ 0) (hsupp : ∃ m : ℤ, ∀ k < m, d k = 0)
    (hneg : ∀ r : ℤ, r < 0 → ∑ᶠ j : ℕ, PowerSeries.coeff j f • d (r - j) = 0) :
    ∀ r : ℤ, r < 0 → d r = 0 := by
  obtain ⟨m, hm⟩ := hsupp
  have key : ∀ t : ℕ, ∀ r : ℤ, r < m + t → r < 0 → d r = 0 := by
    intro t
    induction t with
    | zero => intro r hr _; exact hm r (by simpa using hr)
    | succ t ih =>
      intro r hr hr0
      by_cases hlt : r < m + t
      · exact ih r hlt hr0
      · have hs : ∑ᶠ j : ℕ, PowerSeries.coeff j f • d (r - j) =
            PowerSeries.coeff 0 f • d (r - ((0 : ℕ) : ℤ)) := by
          apply finsum_eq_single _ 0
          intro j hj
          rw [ih (r - j) (by push_cast at hr; omega) (by omega), smul_zero]
        have h := hneg r hr0
        rw [hs, Nat.cast_zero, sub_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
        have h' := congrArg (fun z => (PowerSeries.constantCoeff f)⁻¹ • z) h
        simpa [inv_smul_smul₀ hf] using h'
  intro r hr
  by_cases h : r < m
  · exact hm r h
  · apply key (r - m + 1).toNat r _ hr
    rw [Int.toNat_of_nonneg (by omega)]
    omega

theorem lemGA0_conv_zero {M : Type} [AddCommGroup M] [Module LL M] (f : PowerSeries LL) (d : ℤ → M)
    (hd : ∀ r : ℤ, r < 0 → d r = 0) :
    ∑ᶠ j : ℕ, PowerSeries.coeff j f • d (0 - j) = PowerSeries.constantCoeff f • d 0 := by
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    rw [hd _ (by have : (0 : ℕ) < j := Nat.pos_of_ne_zero hj; omega), smul_zero]

theorem lemGA0_of_tools [NeZero n] (W : LocWach PD LL O v n) {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (C : CmpTie W E ιdR p1 tS zS) (hT : Formalism.MainNotions.CrystallineLiftingInputs.THor W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) :
    LemGA_0 W := by
  intro d T₁ T₂ F b S η m hS i hi y hy hyD la hla x hx hxD hxe
  have hA : Formalism.MainNotions.LiftingTheory.CaseA W := hS.1
  have hp11 : 11 ≤ PD.p := hS.2.1
  have hsur : Formalism.MainNotions.LiftingTheory.Sur W F := hS.2.2.2.2.2.1
  have hcr : IsCrys PD T₂.ρ := by unfold Formalism.MainNotions.LiftingTheory.Sur at hsur; exact hsur.2.1
  have hp0 : (PD.p : LL) ≠ 0 := by
    obtain ⟨ζ, hζ⟩ := hS.2.2.2.2.1
    have hpos : 0 < PD.p := by omega
    have : NeZero PD.p := ⟨hpos.ne'⟩
    exact (hζ.neZero').out

  have hfr : finrank K₀ K = 1 := by
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hA.1).finrank_eq, Module.finrank_self]
  obtain ⟨hcard, -, h9K⟩ := h9 T₂ hcr hA.2.1 hA.2.2
  rw [hfr, Nat.div_one] at hcard
  have h0 : PowerSeries.constantCoeff W.π₀₁ = 0 := lemGA0_cc_π₀₁ W hcard (by omega)
  obtain ⟨-, hmod⟩ := h9K hfr
  have hyI : Formalism.MainNotions.CrystallineLiftingInputs.InI W T₂ (i - 2) y := by
    refine ⟨hyD, ⟨0, 0, by simpa using hy⟩, ?_⟩
    obtain ⟨x', hx', he⟩ := hmod.2 y ⟨hy, hyD.2⟩
    exact ⟨x', hx'.1, hx'.2, by rw [pow_one]; exact he⟩

  have hk : (Formalism.MainNotions.LiftingTheory.qp W ^ 0 * Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S)) • la ∈ W.N T₂ := by
    rw [pow_zero, one_mul, ← hxe]
    exact Submodule.smul_mem _ _ hx
  have hTH := hT hA hp11 2 1 (2 * (hpar n b S + η)) (lemG_sig PD.p (hpar n b S + η))
    (Or.inr ⟨rfl, rfl, rfl⟩) T₂ hcr (i - 2) y la hy hyI hla.1 1 ((PD.p - 1) * 1) 0
    (Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S)) hk (Or.inr ⟨rfl, rfl⟩)
  have hneg := hTH.1
  have h0v := hTH.2 0 (by omega)
  have hi2 : i - 2 + ((2 : ℕ) : ZMod n) = i := by rw [Nat.cast_ofNat, sub_add_cancel]
  have hsub : (⟨(Formalism.MainNotions.LiftingTheory.qp W ^ 0 * Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S)) • la, hk⟩ : ↥(W.N T₂)) =
      (Formalism.MainNotions.LiftingTheory.qp W ^ b i) • (⟨x, hx⟩ : ↥(W.N T₂)) := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, pow_zero, one_mul]
    exact hxe.symm
  rw [hi2, hsub] at hneg h0v
  rw [Nat.cast_zero] at h0v

  have hsm : ∀ r : ℤ, W.levN T₂ i 1 ((Formalism.MainNotions.LiftingTheory.qp W ^ b i) • (⟨x, hx⟩ : ↥(W.N T₂))) r =
      ∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i 1 (Formalism.MainNotions.LiftingTheory.qp W ^ b i)) •
        W.levN T₂ i 1 ⟨x, hx⟩ (r - j) :=
    fun r => W.levN_smul T₂ i 1 _ _ r
  have hccb : PowerSeries.constantCoeff (W.lev i 1 (Formalism.MainNotions.LiftingTheory.qp W ^ b i)) = (PD.p : LL) ^ b i := by
    rw [map_pow, map_pow, lemGA0_cc_qp W i h0]
  have hxneg : ∀ r : ℤ, r < 0 → W.levN T₂ i 1 ⟨x, hx⟩ r = 0 :=
    lemGA0_conv_vanish (W.lev i 1 (Formalism.MainNotions.LiftingTheory.qp W ^ b i)) (W.levN T₂ i 1 ⟨x, hx⟩)
      (by rw [hccb]; exact pow_ne_zero _ hp0) (W.levN_supp T₂ i 1 _)
      (fun r hr => by rw [← hsm r]; exact hneg r hr)
  have he : ((letE i : LetA O n) • (⟨x, hx⟩ : ↥(W.N T₂))) = ⟨x, hx⟩ := Subtype.ext hxD.1
  have hL : W.levN T₂ i 1 ((Formalism.MainNotions.LiftingTheory.qp W ^ b i) • (⟨x, hx⟩ : ↥(W.N T₂))) 0 =
      (PD.p : LL) ^ b i • ιV PD (LL := LL) (V := T₂.V) (W.cmp T₂ ⟨x, hx⟩) := by
    rw [hsm, lemGA0_conv_zero _ _ hxneg, hccb, C.levN_eq, ← C.cmp_eq T₂ hcr i, he]
  have hcch : PowerSeries.coeff 0 (W.lev i 1 (Formalism.MainNotions.LiftingTheory.qp W ^ 0 * Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S))) =
      (PD.p : LL) ^ (b (i - 1) + S) := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, pow_zero, one_mul, map_pow, map_pow,
      lemGA0_cc_pk W C i h0]
  have hmain : (PD.p : LL) ^ b i • W.cmp T₂ ⟨x, hx⟩ =
      (PD.p : LL) ^ (b (i - 1) + S) • ((PD.p : LL) ^ lemG_sig PD.p (hpar n b S + η) •
        (φVB PD (LL := LL) (V := T₂.V))^[2] (W.cmp T₂ ⟨y, hy⟩)) := by
    apply lemGA0_ιV_inj (PD := PD) T₂
    rw [map_smul, map_smul, map_smul, ← hL, h0v, hcch]
  rw [← inv_smul_smul₀ (pow_ne_zero (b i) hp0) (W.cmp T₂ ⟨x, hx⟩), hmain, smul_smul, smul_smul,
    zpow_sub₀ hp0, zpow_add₀ hp0, zpow_natCast, zpow_natCast, zpow_natCast]
  congr 1
  ring

end LemGA0

end Formalism.MainNotions.RamifiedCoefficientChains.S9
end
end

section
noncomputable section

namespace Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open PowerSeries in

def ιS (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) : PowerSeries O →ₐ[O] PowerSeries O :=
  PowerSeries.substAlgHom (R := O) (PowerSeries.HasSubst.of_constantCoeff_zero'
    (Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR))

theorem ιS_apply (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (F : PowerSeries O) :
    ιS W hR F = PowerSeries.subst W.π₀₁ F := by
  rw [ιS, PowerSeries.coe_substAlgHom]

theorem ιS_X (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) : ιS W hR PowerSeries.X = W.π₀₁ := by
  rw [ιS_apply]; exact PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero'
    (Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR))

theorem rep (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) {g : LetA O n} (hg : g ∈ W.AΔ) :
    ∃ F : ZMod n → PowerSeries O, ∀ i, g i = ιS W hR (F i) := by
  obtain ⟨F, hF, -⟩ := hR.2.1 g hg
  exact ⟨F, fun i => by rw [hF i, ιS_apply]; rfl⟩

theorem const_mem (o : ZMod n → O) : (fun i => PowerSeries.C (o i) : LetA O n) ∈ W.AΔ := by
  intro δ _
  funext i
  show W.γ₀ δ (PowerSeries.C (o i)) = PowerSeries.C (o i)
  exact (W.γ₀ δ).commutes (o i)

theorem eq_uniformizer_mul_of_constantCoeff_zero [IsDomain O] (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) {a : LetA O n} (ha : a ∈ W.AΔ)
    (h0 : ∀ i, PowerSeries.constantCoeff (a i) = 0) : ∃ r ∈ W.AΔ, a = W.π₀ * r := by
  have hLR := Formalism.MainNotions.LiftingTheory.lifta_ring_of W hR
  obtain ⟨F, hF⟩ := rep W hR ha
  have hF0 : ∀ i, PowerSeries.constantCoeff (F i) = 0 := by
    intro i
    rw [← Formalism.MainNotions.UnusedSlot80.ToolsR.cc_subst (Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR), ← ιS_apply W hR, ← hF i]
    exact h0 i
  choose F' hF' using fun i => PowerSeries.X_dvd_iff.mpr (hF0 i)
  have he : a = W.π₀ * fun i => ιS W hR (F' i) := by
    funext i
    rw [hF i, hF' i, map_mul, ιS_X]
    rfl
  refine ⟨_, Formalism.MainNotions.LiftingTheory.lifta_divΔ W _ _ hLR.πΔ hLR.πU (he ▸ ha), he⟩

theorem Gd01 : (Gd (O := O) PD.p 0 1) = PowerSeries.X + ((PD.p : ℕ) : PowerSeries O) := by
  simp [Gd]

theorem ιS_qp (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (i : ZMod n) :
    Formalism.MainNotions.LiftingTheory.qp W i = ιS W hR (PowerSeries.X + ((PD.p : ℕ) : PowerSeries O)) := by
  rw [map_add, ιS_X, map_natCast]
  rfl

theorem res_decomp [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    {g : LetA O n} (hg : g ∈ W.AΔ) :
    ∃ (o : ZMod n → O) (g' : LetA O n), g' ∈ W.AΔ ∧
      g = (fun i => PowerSeries.C (o i)) + Formalism.MainNotions.LiftingTheory.qp W * g' := by
  have hLR := Formalism.MainNotions.LiftingTheory.lifta_ring_of W hR
  obtain ⟨F, hF⟩ := rep W hR hg
  choose Q R hQR hRd using fun i => wdiv hlm 0 1 (F i)
  have hRc : ∀ i, (R i : PowerSeries O) = PowerSeries.C ((R i).coeff 0) := by
    intro i
    have h1 : (R i).degree ≤ 0 := Nat.WithBot.lt_one_iff_le_zero.mp (by simpa using hRd i)
    conv_lhs => rw [Polynomial.eq_C_of_degree_le_zero h1]
    simp
  have he : g = (fun i => PowerSeries.C ((R i).coeff 0)) + Formalism.MainNotions.LiftingTheory.qp W * fun i => ιS W hR (Q i) := by
    funext i
    rw [Pi.add_apply, Pi.mul_apply, hF i, hQR i, Gd01, map_add, map_mul, ← ιS_qp, hRc i]
    rw [show ιS W hR (PowerSeries.C ((R i).coeff 0)) = PowerSeries.C ((R i).coeff 0) from
      (ιS W hR).commutes _]
    ring
  refine ⟨_, _, Formalism.MainNotions.LiftingTheory.lifta_divΔ W _ _ (Formalism.MainNotions.LiftingTheory.lifta_qΔ W hLR.πΔ) hLR.qU ?_, he⟩
  have : Formalism.MainNotions.LiftingTheory.qp W * (fun i => ιS W hR (Q i)) = g - fun i => PowerSeries.C ((R i).coeff 0) := by
    rw [he]; ring
  rw [this]
  exact W.AΔ.sub_mem hg (const_mem W _)

theorem res_unique [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    (o : ZMod n → O) {g : LetA O n} (hg : g ∈ W.AΔ)
    (h : (fun i => PowerSeries.C (o i) : LetA O n) = Formalism.MainNotions.LiftingTheory.qp W * g) : o = 0 := by
  have hLR := Formalism.MainNotions.LiftingTheory.lifta_ring_of W hR
  obtain ⟨G, hG⟩ := rep W hR hg
  have ha : (fun i => PowerSeries.C (o i) : LetA O n) ∈ W.AΔ := const_mem W o
  obtain ⟨f0, -, huniq⟩ := hR.2.1 _ ha
  have h1 : ∀ i, (fun i => PowerSeries.C (o i) : LetA O n) i =
      PowerSeries.subst (W.π₀ i) (PowerSeries.C (o i)) := by
    intro i
    show PowerSeries.C (o i) = PowerSeries.subst W.π₀₁ (PowerSeries.C (o i))
    rw [← ιS_apply W hR]
    exact ((ιS W hR).commutes _).symm
  have h2 : ∀ i, (fun i => PowerSeries.C (o i) : LetA O n) i =
      PowerSeries.subst (W.π₀ i) ((PowerSeries.X + ((PD.p : ℕ) : PowerSeries O)) * G i) := by
    intro i
    show _ = PowerSeries.subst W.π₀₁ _
    rw [← ιS_apply W hR, map_mul, ← ιS_qp, ← hG i, h]
    rfl
  have e := congrFun ((huniq _ h1).trans (huniq _ h2).symm)
  funext i
  have hP := wuniq hlm 0 1 (Polynomial.C (o i)) (lt_of_le_of_lt Polynomial.degree_C_le (by simp))
    (G i) (by rw [Polynomial.coe_C, Gd01]; exact e i)
  simpa using hP

section Gam

variable {R : Type} [CommRing R] [BinomialRing R] [Algebra R O]

theorem qZ (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) :
    ∃ w : (LetA O n)ˣ, ∀ i, (1 + PowerSeries.X : PowerSeries O) ^ (PD.p ^ 1) - 1 =
      PowerSeries.X * ((w : LetA O n) i * Formalism.MainNotions.LiftingTheory.qp W i) := by
  obtain ⟨w, hw⟩ := (Formalism.MainNotions.LiftingTheory.lifta_ring_of W hR).qq
  refine ⟨w, fun i => ?_⟩
  rw [pow_one, ← W.q₀_def]
  congr 1
  exact congrFun hw i

theorem autW [IsDomain O] [CharZero O] (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (z : R)
    (hz : ((W.χΓ W.gam : Oˣ) : O) = algebraMap R O z) (hz1 : ((PD.p : ℕ) : R) ∣ z - 1) :
    (∀ f, ∃ H, W.γ₀ W.gam f - f = ((1 + PowerSeries.X) ^ (PD.p ^ 1) - 1) * H) ∧
    (∀ P Rr : PowerSeries O, P * Rr = (1 + PowerSeries.X) ^ (PD.p ^ 1) - 1 →
      ∃ H, W.γ₀ W.gam P - algebraMap O (PowerSeries O) (algebraMap R O z) * P = P ^ 2 * H) := by
  have hl : 2 ≤ PD.p := PD.hp.two_le
  obtain ⟨m, hm⟩ := hz1
  have hc : z = 1 + ((PD.p : ℕ) : R) ^ 1 * m := by rw [pow_one, ← hm]; ring
  have h1 : PowerSeries.coeff 1 (W.γ₀ W.gam PowerSeries.X) = algebraMap R O z := by
    rw [(W.γ₀_X W.gam).2, hz]
  exact Formalism.MainNotions.UnusedSlot80.LG.aut_core W.φ₀ (W.γ₀ W.gam) PD.p hl (Formalism.MainNotions.UnusedSlot80.LG.φ₀_X_eq W) (W.γ₀_comm _)
    (W.γ₀_X W.gam).1 z m 1 hc h1

theorem hγg_of [IsDomain O] [CharZero O] (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (z : R)
    (hz : ((W.χΓ W.gam : Oˣ) : O) = algebraMap R O z) (hz1 : ((PD.p : ℕ) : R) ∣ z - 1) :
    ∀ g ∈ W.AΔ, ∃ g' ∈ W.AΔ, W.γA W.gam g - g = W.π₀ * Formalism.MainNotions.LiftingTheory.qp W * g' := by
  have hLR := Formalism.MainNotions.LiftingTheory.lifta_ring_of W hR
  obtain ⟨hA, -⟩ := autW W hR z hz hz1
  obtain ⟨w, hZ⟩ := qZ W hR
  intro g hg
  choose H hH using fun i => hA (g i)
  set t : LetA O n := fun i => PowerSeries.X * ((w : LetA O n) i * H i)
  have ht : W.γA W.gam g - g = Formalism.MainNotions.LiftingTheory.qp W * t := by
    funext i
    show W.γ₀ W.gam (g i) - g i = Formalism.MainNotions.LiftingTheory.qp W i * t i
    rw [hH i, hZ i]
    simp only [t]
    ring
  have htA : t ∈ W.AΔ := Formalism.MainNotions.LiftingTheory.lifta_divΔ W _ t (Formalism.MainNotions.LiftingTheory.lifta_qΔ W hLR.πΔ) hLR.qU
    (ht ▸ W.AΔ.sub_mem (Formalism.MainNotions.LiftingTheory.tr_γA_mem W W.gam hg) hg)
  obtain ⟨r, hr, hrt⟩ := eq_uniformizer_mul_of_constantCoeff_zero W hR htA (fun i => by simp [t])
  exact ⟨r, hr, by rw [ht, hrt]; ring⟩

theorem hγq_of [IsDomain O] [CharZero O] (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (z : R)
    (hz : ((W.χΓ W.gam : Oˣ) : O) = algebraMap R O z) (hz1 : ((PD.p : ℕ) : R) ∣ z - 1) :
    ∃ r ∈ W.AΔ, W.γA W.gam (Formalism.MainNotions.LiftingTheory.qp W) =
      (algebraMap O (LetA O n) (W.χΓ W.gam : O) + Formalism.MainNotions.LiftingTheory.qp W * r) * Formalism.MainNotions.LiftingTheory.qp W := by
  have hLR := Formalism.MainNotions.LiftingTheory.lifta_ring_of W hR
  obtain ⟨-, hB⟩ := autW W hR z hz hz1
  obtain ⟨w, hZ⟩ := qZ W hR
  choose H hH using fun i => hB (Formalism.MainNotions.LiftingTheory.qp W i) (PowerSeries.X * (w : LetA O n) i) (by rw [hZ i]; ring)
  have hq := Formalism.MainNotions.LiftingTheory.lifta_qΔ W hLR.πΔ
  have he : W.γA W.gam (Formalism.MainNotions.LiftingTheory.qp W) =
      (algebraMap O (LetA O n) (W.χΓ W.gam : O) + Formalism.MainNotions.LiftingTheory.qp W * fun i => H i) * Formalism.MainNotions.LiftingTheory.qp W := by
    funext i
    show W.γ₀ W.gam (Formalism.MainNotions.LiftingTheory.qp W i) = _
    rw [sub_eq_iff_eq_add.mp (hH i), Pi.mul_apply, Pi.add_apply, Pi.mul_apply, Pi.algebraMap_apply, hz]
    ring
  refine ⟨fun i => H i, ?_, he⟩
  apply Formalism.MainNotions.LiftingTheory.lifta_divΔ W (Formalism.MainNotions.LiftingTheory.qp W ^ 2) _ (W.AΔ.pow_mem hq 2) (by rw [map_pow]; exact hLR.qU.pow 2)
  have : Formalism.MainNotions.LiftingTheory.qp W ^ 2 * (fun i => H i) =
      W.γA W.gam (Formalism.MainNotions.LiftingTheory.qp W) - algebraMap O (LetA O n) (W.χΓ W.gam : O) * Formalism.MainNotions.LiftingTheory.qp W := by
    rw [he]; ring
  rw [this]
  exact W.AΔ.sub_mem (Formalism.MainNotions.LiftingTheory.tr_γA_mem W W.gam hq) (W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) hq)

theorem hγp_of [IsDomain O] [CharZero O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (hl0 : ((PD.p : ℕ) : O) ≠ 0)
    (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (z : R)
    (hz : ((W.χΓ W.gam : Oˣ) : O) = algebraMap R O z) (hz1 : ((PD.p : ℕ) : R) ∣ z - 1) :
    ∃ r ∈ W.AΔ, W.γA W.gam (Formalism.MainNotions.LiftingTheory.pk W 1) =
      (1 + W.π₀ * Formalism.MainNotions.LiftingTheory.qp W * r) * Formalism.MainNotions.LiftingTheory.pk W 1 := by
  have hLR := Formalism.MainNotions.LiftingTheory.lifta_ring_of W hR
  have hl : 2 ≤ PD.p := PD.hp.two_le
  have hπ := hLR.πΔ
  have hq := Formalism.MainNotions.LiftingTheory.lifta_qΔ W hπ
  set qp := Formalism.MainNotions.LiftingTheory.qp W
  set p1 := Formalism.MainNotions.LiftingTheory.pk W 1
  have hp1 : p1 = W.φA qp := by simp [p1, Formalism.MainNotions.LiftingTheory.pk]; rfl
  have hp1A : p1 ∈ W.AΔ := by rw [hp1]; exact Formalism.MainNotions.LiftingTheory.lifta_φΔ W _ hq
  obtain ⟨rq, hrq, hγq⟩ := hγq_of W hR z hz hz1
  set χ : LetA O n := algebraMap O (LetA O n) (W.χΓ W.gam : O)
  set u : LetA O n := χ + p1 * W.φA rq
  have huA : u ∈ W.AΔ := W.AΔ.add_mem (W.AΔ.algebraMap_mem _) (W.AΔ.mul_mem hp1A (Formalism.MainNotions.LiftingTheory.lifta_φΔ W _ hrq))
  have hγp1 : W.γA W.gam p1 = u * p1 := by
    rw [hp1, ← W.φA_γA, hγq, map_mul, map_add, map_mul]
    simp only [u, χ, AlgHom.commutes]
    rw [← hp1]
  obtain ⟨g', hg', hγg'⟩ := hγg_of W hR z hz hz1 p1 hp1A
  have hu1 : (u - 1) * p1 = W.π₀ * qp * g' := by rw [← hγg', hγp1]; ring
  obtain ⟨t, ht, hφπ⟩ := hLR.φπ
  have hp1e : p1 = ((PD.p : ℕ) : LetA O n) + W.π₀ * qp ^ (PD.p - 1) * t := by
    rw [hp1, show qp = W.π₀ + ((PD.p : ℕ) : LetA O n) from rfl, map_add, hφπ, map_natCast]
    simp only [Formalism.MainNotions.LiftingTheory.qp]
    ring
  obtain ⟨o, a, ha, hua⟩ := res_decomp W hlm hR (W.AΔ.sub_mem huA W.AΔ.one_mem)
  have hqp : qp ^ (PD.p - 1) = qp * qp ^ (PD.p - 2) := by rw [← pow_succ']; congr 1; omega

  have ho : o = 0 := by
    have hC : (fun i => PowerSeries.C (o i * ((PD.p : ℕ) : O)) : LetA O n) =
        qp * (W.π₀ * g' - a * p1 - (fun i => PowerSeries.C (o i)) * (W.π₀ * qp ^ (PD.p - 2) * t)) := by
      have e1 : (fun i => PowerSeries.C (o i * ((PD.p : ℕ) : O)) : LetA O n) =
          (fun i => PowerSeries.C (o i)) * ((PD.p : ℕ) : LetA O n) := by
        funext i; simp [map_mul]
      rw [e1]
      have e2 := hu1
      rw [hua, hp1e] at e2
      rw [hp1e, hqp] at *
      linear_combination e2
    have := res_unique W hlm hR _ (W.AΔ.sub_mem (W.AΔ.sub_mem (W.AΔ.mul_mem hπ hg') (W.AΔ.mul_mem ha hp1A))
      (W.AΔ.mul_mem (const_mem W o) (W.AΔ.mul_mem (W.AΔ.mul_mem hπ (W.AΔ.pow_mem hq _)) ht))) hC
    funext i
    have hi := congrFun this i
    simp only [Pi.zero_apply] at hi ⊢
    exact (mul_eq_zero.mp hi).resolve_right hl0
  have hua' : u - 1 = qp * a := by
    rw [hua, ho]
    have : (fun i => PowerSeries.C ((0 : ZMod n → O) i) : LetA O n) = 0 := by funext i; simp
    rw [this, zero_add]

  have hap : a * p1 = W.π₀ * g' := by
    apply Formalism.MainNotions.LiftingTheory.lifta_reg W qp _ _ hLR.qU
    rw [← mul_assoc, ← hua', hu1]; ring
  have ha0 : ∀ i, PowerSeries.constantCoeff (a i) = 0 := by
    intro i
    have e := congrArg (fun x : LetA O n => PowerSeries.constantCoeff (x i)) hap
    simp only [Pi.mul_apply, map_mul] at e
    have hcp : PowerSeries.constantCoeff (p1 i) = ((PD.p : ℕ) : O) := by
      rw [hp1e]
      simp [LocWach.π₀, Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR]
    have hcπ : PowerSeries.constantCoeff (W.π₀ i) = 0 := Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR
    rw [hcp, hcπ, zero_mul] at e
    exact (mul_eq_zero.mp e).resolve_right hl0
  obtain ⟨r, hr, har⟩ := eq_uniformizer_mul_of_constantCoeff_zero W hR ha ha0
  refine ⟨r, hr, ?_⟩
  rw [hγp1, show u = 1 + (u - 1) by ring, hua', har]
  ring

end Gam

theorem hAq'_of [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) :
    ∀ i (g : LetA O n), g ∈ W.AΔ → (letE i : LetA O n) * g = g →
      ∃ (o : O) (g' : LetA O n), g' ∈ W.AΔ ∧
        g = algebraMap O (LetA O n) o * letE i + Formalism.MainNotions.LiftingTheory.qp W * g' := by
  intro i g hg hgi
  obtain ⟨o, g', hg', he⟩ := res_decomp W hlm hR hg
  refine ⟨o i, letE i * g', W.AΔ.mul_mem (Formalism.MainNotions.LiftingTheory.idempotent_mem_invariants W i) hg', ?_⟩
  rw [← hgi]
  conv_lhs => rw [he]
  have e : (letE i : LetA O n) * (fun j => PowerSeries.C (o j)) = algebraMap O (LetA O n) (o i) * letE i := by
    funext j
    by_cases h : j = i
    · subst h; simp [letE]
    · simp [letE, h]
  rw [mul_add, e]
  ring

theorem hqc'_of [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) :
    ∀ i (o : O) (g : LetA O n), g ∈ W.AΔ → (letE i : LetA O n) * g = g →
      algebraMap O (LetA O n) o * letE i = Formalism.MainNotions.LiftingTheory.qp W * g → o = 0 := by
  intro i o g hg _ h
  have e : algebraMap O (LetA O n) o * letE i =
      (fun j => PowerSeries.C (if j = i then o else 0) : LetA O n) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [letE]
    · simp [letE, hj]
  rw [e] at h
  have := congrFun (res_unique W hlm hR _ hg h) i
  simpa using this

theorem uniformizer_unit_of_binomial_ring [IsDomain O] [CharZero O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (hl0 : ((PD.p : ℕ) : O) ≠ 0)
    (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) {R : Type} [CommRing R] [BinomialRing R] [Algebra R O] (z : R)
    (hz : ((W.χΓ W.gam : Oˣ) : O) = algebraMap R O z) (hz1 : ((PD.p : ℕ) : R) ∣ z - 1) :
    IsUnit (algebraMap (LetA O n) W.EE W.π₀) ∧
    IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) ∧
    (∀ g ∈ W.AΔ, ∃ g' ∈ W.AΔ, W.γA W.gam g - g = W.π₀ * Formalism.MainNotions.LiftingTheory.qp W * g') ∧
    (∃ r ∈ W.AΔ, W.γA W.gam (Formalism.MainNotions.LiftingTheory.qp W) =
      (algebraMap O (LetA O n) (W.χΓ W.gam : O) + Formalism.MainNotions.LiftingTheory.qp W * r) * Formalism.MainNotions.LiftingTheory.qp W) ∧
    (∃ r ∈ W.AΔ, W.γA W.gam (Formalism.MainNotions.LiftingTheory.pk W 1) =
      (1 + W.π₀ * Formalism.MainNotions.LiftingTheory.qp W * r) * Formalism.MainNotions.LiftingTheory.pk W 1) ∧
    (∀ (i : ZMod n) (g : LetA O n), g ∈ W.AΔ → (letE i : LetA O n) * g = g →
      ∃ (o : O) (g' : LetA O n), g' ∈ W.AΔ ∧
        g = algebraMap O (LetA O n) o * letE i + Formalism.MainNotions.LiftingTheory.qp W * g') ∧
    (∀ (i : ZMod n) (o : O) (g : LetA O n), g ∈ W.AΔ → (letE i : LetA O n) * g = g →
      algebraMap O (LetA O n) o * letE i = Formalism.MainNotions.LiftingTheory.qp W * g → o = 0) := by
  have hLR := Formalism.MainNotions.LiftingTheory.lifta_ring_of W hR
  exact ⟨hLR.πU, hLR.qU, hγg_of W hR z hz hz1, hγq_of W hR z hz hz1, hγp_of W hlm hl0 hR z hz hz1,
    hAq'_of W hlm hR, hqc'_of W hlm hR⟩

end Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData

namespace Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

set_option maxHeartbeats 400000 in

theorem gamma_lemma_of_crystalline (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) :
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], Formalism.MainNotions.N.Pv.LocalLengthBound.WachGammaDerivation ((HW l).W K 1 LL hg) := by
  intro l _ K LL hg _
  have h9W : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K 1 LL hg) := h9 l K 1 LL hg
  refine fun d T₁ T₂ F' b S η m hset => ?_
  have hCA : Formalism.MainNotions.LiftingTheory.CaseA ((HW l).W K 1 LL hg) := hset.1
  have hT₂ : IsCrys ((D.loc l).PD K) T₂.ρ := hset.2.2.2.2.2.1.2.1
  have hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP ((HW l).W K 1 LL hg) :=
    (Formalism.MainNotions.LiftingTheory.frame_p9A ((HW l).W K 1 LL hg) h9W hCA T₂ hT₂).1
  haveI : CharZero ↥(OL LL) := Formalism.MainNotions.UnusedSlot80.levg_charZero LL
  letI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) :=
    Formalism.MainNotions.CrystallineLiftingInputs.OL.OL_complete_max (D.loc l) LL
  have hlm : (((((D.loc l).PD K).p : ℕ)) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
    rw [(D.loc l).PD_p K]; exact Formalism.MainNotions.CrystallineLiftingInputs.OL.l_mem_max (D.loc l) LL
  have hl0 : (((((D.loc l).PD K).p : ℕ)) : ↥(OL LL)) ≠ 0 := by
    rw [(D.loc l).PD_p K]; exact Formalism.MainNotions.CrystallineLiftingInputs.OL.l_ne_zero LL
  obtain ⟨z, hz, hz1⟩ := Formalism.MainNotions.UnusedSlot80.levg_chi (D.loc l) (HW l) K LL hg
  obtain ⟨hπU, hqU, hγg, hγq, hγp, hAq, hqc⟩ := uniformizer_unit_of_binomial_ring ((HW l).W K 1 LL hg) hlm hl0 hR z hz hz1
  exact Formalism.MainNotions.N.Pv.LocalLengthBound.gamma_structure_of ((HW l).W K 1 LL hg) h9W hπU hqU hγg hγq hγp hAq hqc d T₁ T₂ F' b S η m hset

end Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData
end
end

section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.Asm

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O]
    [Algebra Zl Ai] {RW : Type} [CommRing RW] [Algebra O RW] {inclR : (TensorProduct Zl O Ai) →ₐ[O] RW}
    {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : TensorProduct Zl O Ai}
    {E : EtTie W (TensorProduct Zl O Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}

theorem content_bound_level_of_dcris_exact [NeZero n] {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (h4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hLev : Formalism.MainNotions.LiftingTheory.CaseA W → 11 ≤ PD.p → Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W)
    (hpt : Formalism.MainNotions.LiftingTheory.CaseA W → 11 ≤ PD.p → ∀ (c : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
      ∃ τ : K →ₐ[Qp] LL, Pt c ζ τ)
    (hT2 : Formalism.MainNotions.CrystallineLiftingInputs.TTool2 W) (hTH : Formalism.MainNotions.CrystallineLiftingInputs.THor W) (hGs : LemmaGs W)
    (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) : Formalism.MainNotions.N.Pv.LocalLengthBound.ContentBoundLevel W := by
  intro d T₁ T₂ F' b S η m hset
  have hCA := hset.1
  have h11 := hset.2.1
  exact Formalism.MainNotions.N.Pv.LocalLengthBound.contentBoundLevel_of W h5 h9 (hLev hCA h11)
    (fun T hT c ζ hζ x k hk j hj => by
      obtain ⟨τ, hτ⟩ := hpt hCA h11 c ζ hζ
      exact (((h4 T hT).2 c ζ τ hτ).1.1 x k hk j).2 hj)
    hT2 hTH hGs hE hC hQ d T₁ T₂ F' b S η m hset

theorem frobenius_lift_lemmas_general [NeZero n] (h1 : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeFree W) (h3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (Ct : CmpTie W E ιdR p1 tS zS)
    (hLev : Formalism.MainNotions.LiftingTheory.CaseA W → 11 ≤ PD.p → Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W)
    (hPT : Formalism.MainNotions.LiftingTheory.CaseA W → 11 ≤ PD.p → Formalism.MainNotions.N.Pv.LocalLengthBound.PtTrans W)
    (hH2 : Formalism.MainNotions.N.Pv.LocalLengthBound.H2Bound W) (hL41 : Formalism.MainNotions.N.Pv.LocalLengthBound.ContentBoundLevel W) (hDN : LemmaDN W)
    (hDN0 : Formalism.MainNotions.N.Pv.LocalLengthBound.LemmaDN0 W) : WachVectorLiftingBound W := by
  intro d T₁ T₂ F' b S η m hset
  have hCA := hset.1
  have h11 := hset.2.1
  obtain ⟨_, -, hFrac⟩ := hset.2.2.2.1
  have hL := hLev hCA h11
  have hMC := Formalism.MainNotions.N.Pv.LocalLengthBound.memCrit_of W hCA hFrac h1 h3 hL h5 hQ
  have hG := Formalism.MainNotions.N.Pv.LocalLengthBound.gam_of_tie W hCA.2.1 Ct
  have hGΔ := Formalism.MainNotions.N.Pv.LocalLengthBound.gamΔ_of_tie W Ct
  have hP := hPT hCA h11
  refine Formalism.MainNotions.N.Pv.LocalLengthBound.length_bound_of_hypotheses W h3 h5 h9 hL hE hC hQ hMC hH2 hL41 hDN hDN0
    (((W.χΓ W.gam).isUnit.map (algebraMap O LL)).ne_zero) (Formalism.MainNotions.N.Pv.LocalLengthBound.chi_zpow_ne_one W hCA)
    (fun T hT c ζ hζ x hx hγx k => hG.1 T hT c ζ hζ ⟨x, hx⟩ hγx k) hG.2 ?_ d T₁ T₂ F' b S η m hset
  intro T hT c ζ ζ₀ hζ hζ₀
  obtain ⟨δ, hδ, a, hζa, hv⟩ := hP ζ ζ₀ hζ hζ₀
  exact ⟨δ, hδ, algebraMap O LL (W.χΓ δ : O), ((W.χΓ δ).isUnit.map (algebraMap O LL)).ne_zero,
    fun x hx k => hGΔ T hT c ζ ζ₀ δ a hζ hζa hv x hx k,
    fun f => Ct.lev_Γ δ c ζ ζ₀ 1 a (by rwa [pow_one]) hv hζa f⟩

end Gen

section Rec

variable (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)

theorem caseA_loc {l : ℕ} [Fact l.Prime] {K LL : Loc.FinExt l} (hg : Loc.Good K 1 LL)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA ((HW l).W K 1 LL hg)) : Loc.CaseA K LL := by
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  refine ⟨fun x hx => ?_, by rw [← hpl]; exact hCA.2.2, hg⟩
  obtain ⟨y, hy⟩ := hCA.1.2 ⟨x, hx⟩
  have h2 := y.2.2
  have : ((y : ↥(K0 K)) : Om l) = x := congrArg Subtype.val hy
  rw [this] at h2
  exact h2

variable {CR CA CB CK : ℝ}

theorem crystalline_clause_of_admitted (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.DeltaInvariantLattices.P3 D HW F Cm :=
  fun l _ K s LL h => (hA.1 l K s LL h).2.2.1

theorem laurent_clause_of_admitted (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm :=
  fun l _ K s LL h => (hA.1 l K s LL h).2.2.2.1

theorem gamma_sub_one_in_coordinates (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F :=
  fun l _ K s LL h => (hA.1 l K s LL h).2.2.2.2.2.2.2.2.1

theorem level_tools_of_admitted (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.WachCoordinates.adm7 D HW F Cm :=
  Formalism.MainNotions.UnusedSlot80.tools_unramified_statement D HW F Cm ⟨crystalline_clause_of_admitted D HW F Cm hA, laurent_clause_of_admitted D HW F Cm hA, gamma_sub_one_in_coordinates D HW F Cm hA⟩

theorem truncation_clause_of_admitted (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.CrystallineLiftingInputs.adm15 D HW F Cm := by
  refine ⟨Formalism.MainNotions.CrystallineLiftingInputs.TToolAlg_holds, fun l _ K LL hg _ => ?_⟩
  have hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K 1 LL hg) := (hA.1 l K 1 LL hg).2.2.2.2.2.2.2.2.1
  have hinj : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hO2 : ∀ x : ↥LL.1, 0 ≤ (D.loc l).v LL x → ∃ o : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 o = x :=
    fun x hx => ⟨⟨x, ((D.loc l).v_O LL x).1 hx⟩, rfl⟩
  haveI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := Formalism.MainNotions.RamifiedCoefficientChains.S9.DLev.complete_max LL
  have hlm : (((((D.loc l).PD K).p : ℕ)) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
    rw [(D.loc l).PD_p K]; exact Formalism.BasicNotions.Examples₂.LB.l_mem_max LL
  exact ⟨Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData.tTool1_of _ hinj hO2 hP9 (hA.2.2.2.2.2.2.2.1 l K 1 LL hg),
    Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData.tTool2_of _ hinj hO2 hlm hP9 (hA.2.2.2.2.2.2.2.1 l K 1 LL hg) (hA.2.2.2.2.2.2.2.2.1 l K 1 LL hg)⟩

theorem rhoLift_of_Adm (hA : admitted D HW F Cm CR CA CB CK) : rhoLift D HW F :=
  Formalism.MainNotions.N.Pv.LocalLengthBound.rhoLift_D D HW F Cm CR CA CB CK hA fun l _ K LL hg _ =>
    ⟨((truncation_clause_of_admitted D HW F Cm hA).2 l K LL hg).2, Formalism.MainNotions.CrystallineLiftingInputs.Tools.local_clause_of_admitted_statements D HW F Cm hA l K LL hg⟩

set_option maxHeartbeats 1600000 in

theorem h2_bound_of_admitted (hA : admitted D HW F Cm CR CA CB CK) (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l)
    (hg : Loc.Good K 1 LL) [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))] :
    Formalism.MainNotions.N.Pv.LocalLengthBound.H2Bound ((HW l).W K 1 LL hg) := by
  intro d T₁ T₂ F' b S η m hset
  have hCA : Formalism.MainNotions.LiftingTheory.CaseA ((HW l).W K 1 LL hg) := hset.1
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hCAl : Loc.CaseA K LL := caseA_loc D HW hg hCA
  have h5l : 5 ≤ l := by have := hset.2.1; rw [hpl] at this; omega
  have h1 := hA.1 l K 1 LL hg
  obtain ⟨hE, hC, hQ⟩ := hA.2.2.2.2.2.2.2.2.2.2.1 l K LL
  have hs : ((HW l).W K 1 LL hg).s = 1 := hCA.2.1
  have C := ((Cm l).C K 1 LL hg).tie
  have hG := Formalism.MainNotions.N.Pv.LocalLengthBound.gam_of_tie _ hs C
  have hLev : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration ((HW l).W K 1 LL hg) := (level_tools_of_admitted D HW F Cm hA l K LL hCAl h5l).2
  haveI : IsAdicComplete (Ideal.span {((((D.loc l).PD K).p : ℕ) : ↥(OL LL))}) ↥(OL LL) :=
    Formalism.MainNotions.UnusedSlot80.eq_sum_herm_smul_frame_of_inW (D.loc l) K LL
  have hΔ : IsUnit ((((HW l).W K 1 LL hg).DelF.card : ℕ) : ↥(OL LL)) := by
    haveI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
    have hcard : ((HW l).W K 1 LL hg).DelF.card = l - 1 :=
      Formalism.MainNotions.UnusedSlot80.LevR.card_delF D HW F (gamma_sub_one_in_coordinates D HW F Cm hA) l K LL hCAl
    by_contra hnu
    have hm : ((((HW l).W K 1 LL hg).DelF.card : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := hnu
    have hlm := Formalism.BasicNotions.Examples₂.LB.l_mem_max LL
    have e : ((l : ℕ) : ↥(OL LL)) - ((((HW l).W K 1 LL hg).DelF.card : ℕ) : ↥(OL LL)) = 1 := by
      rw [hcard, Nat.cast_sub (by omega)]; simp
    have h3 := Submodule.sub_mem _ hlm hm
    rw [e] at h3
    exact (IsLocalRing.maximalIdeal.isMaximal ↥(OL LL)).ne_top ((Ideal.eq_top_iff_one _).2 h3)
  exact Formalism.MainNotions.N.Pv.LocalLengthBound.h2Bound_of_hypotheses _ Subtype.val_injective hΔ Formalism.MainNotions.CrystallineLiftingInputs.power_series_dvr_factorisation h1.2.2.2.2.1
    h1.2.2.2.2.2.2.2.2.1 hLev ((truncation_clause_of_admitted D HW F Cm hA).2 l K LL hg).2
    (Formalism.MainNotions.CrystallineLiftingInputs.Tools.frobenius_power_congruence_of_admitted D HW F Cm hA l K LL hg) hE hC hQ
    ((((HW l).W K 1 LL hg).χΓ ((HW l).W K 1 LL hg).gam).isUnit.map (algebraMap _ ↥LL.1)).ne_zero
    (Formalism.MainNotions.N.Pv.LocalLengthBound.chi_zpow_ne_one _ hCA)
    (fun T hT c ζ hζ x hx hγx k => hG.1 T hT c ζ hζ ⟨x, hx⟩ hγx k) hG.2 d T₁ T₂ F' b S η m hset

set_option maxHeartbeats 1600000 in

theorem lemGA_rec (hA : admitted D HW F Cm CR CA CB CK) (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l)
    (hg : Loc.Good K 1 LL) [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))] :
    LemGA ((HW l).W K 1 LL hg) := by
  have h9 := (hA.1 l K 1 LL hg).2.2.2.2.2.2.2.2.1
  have h5 := (hA.1 l K 1 LL hg).2.2.2.2.1
  have hT2 := ((truncation_clause_of_admitted D HW F Cm hA).2 l K LL hg).2
  have hTH := Formalism.MainNotions.CrystallineLiftingInputs.Tools.frobenius_power_congruence_of_admitted D HW F Cm hA l K LL hg
  obtain ⟨hE, hC, hQ⟩ := hA.2.2.2.2.2.2.2.2.2.2.1 l K LL
  have hP9 := gamma_sub_one_in_coordinates D HW F Cm hA
  have hLev := Formalism.MainNotions.UnusedSlot80.levCoeff_of_pt D HW F Cm (laurent_clause_of_admitted D HW F Cm hA) (Formalism.MainNotions.UnusedSlot80.points_exist_of_ring_condition D HW F hP9)
  have hB : ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))], Formalism.MainNotions.RamifiedCoefficientChains.Sh.BasTool ((HW l).W K 1 LL hg) := by
    intro l _ K LL hg _
    haveI : IsFractionRing ↥(OL LL) ↥LL.1 := Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL
    exact Formalism.MainNotions.RamifiedCoefficientChains.Sh.basTool_of _ (hA.1 l K 1 LL hg).2.2.2.2.2.2.2.2.1
  have hEC := Formalism.MainNotions.N.Pv.LocalLengthBound.expCrit_D' D HW F Cm CR CA CB CK hA hLev hB
  have hCT := ((Cm l).C K 1 LL hg).tie
  intro d T₁ T₂ F' b S η m hS
  have hCA := hS.1
  have hl11 : 11 ≤ ((D.loc l).PD K).p := hS.2.1
  rw [(D.loc l).PD_p K] at hl11
  have hrec : Loc.CaseA K LL := caseA_loc D HW hg hCA
  have hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP ((HW l).W K 1 LL hg) :=
    Formalism.MainNotions.UnusedSlot80.ring_condition_uniformizer_polynomial D HW F hP9 l K LL hrec
  obtain ⟨hGN, hGA⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.gam_of_tie ((HW l).W K 1 LL hg) hCA.2.1 hCT
  have hER : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRing ((HW l).W K 1 LL hg) :=
    Formalism.MainNotions.N.Pv.LocalLengthBound.expRing_of ((HW l).W K 1 LL hg) hR
  have h4L : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration ((HW l).W K 1 LL hg) := hLev l K LL hrec (by omega)
  have hEU : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules ((HW l).W K 1 LL hg) :=
    Formalism.MainNotions.N.Pv.LocalLengthBound.expRules_of ((HW l).W K 1 LL hg) h4L hGN hGA
  have hla : LemGA_la ((HW l).W K 1 LL hg) :=
    lemGA_la_of_adm ((HW l).W K 1 LL hg) hT2 h9 h5 hE hC hQ
  have hlR : Formalism.MainNotions.LiftingTheory.lifta_Ring ((HW l).W K 1 LL hg) :=
    liftRing_of_uniformizer_clause ((HW l).W K 1 LL hg) h9 hCA T₂ hS.2.2.2.2.2.1.2.1
  have hx : GammaActionLemma ((HW l).W K 1 LL hg) :=
    lemGA_x_of ((HW l).W K 1 LL hg) hER hEU (hEC l K LL hrec (by omega)) hTH h9 h5 hlR
      (jumps_in_letter_of_crystalline ((HW l).W K 1 LL hg) hE hC hQ)
  have h0 : LemGA_0 ((HW l).W K 1 LL hg) := lemGA0_of_tools ((HW l).W K 1 LL hg) hCT hTH h9
  exact lemGA_of_pieces ((HW l).W K 1 LL hg) hla hx h0 d T₁ T₂ F' b S η m hS

theorem lemGB_rec (hA : admitted D HW F Cm CR CA CB CK) (h23 : Formalism.MainNotions.LiftingTheory.adm23 D HW F)
    (hC4 : Formalism.MainNotions.N.LetterConditionGlobal D HW F) (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l)
    (hg : Loc.Good K 1 LL) [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))] :
    LemGB ((HW l).W K 1 LL hg) := by
  have hQ := Formalism.MainNotions.CrystallineLiftingInputs.Tools.level_clause_of_admitted_statements D HW F Cm hA h23 l K LL hg
  have h9 := (hA.1 l K 1 LL hg).2.2.2.2.2.2.2.2.1
  refine lemGB_of _ hQ (fun hCA => Formalism.MainNotions.CrystallineLiftingInputs.RToolNum_holds (D.loc l) (HW l) K LL hg hCA)
    (hC4 l K 1 LL hg) h9 (Formalism.MainNotions.LiftingTheory.lattice_clause_every_situation D HW F l K 1 LL hg)
    (fun _ => lemmaGD_cc (HW l) hg) (fun _ => ?_)
    (Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData.gamma_lemma_of_crystalline D HW F (gamma_sub_one_in_coordinates D HW F Cm hA) l K LL hg)
  rw [(D.loc l).PD_p K]
  exact Formalism.MainNotions.UnusedSlot80.Split2.isUnit_pred l LL

theorem lemmaGs_rec (hA : admitted D HW F Cm CR CA CB CK) (h23 : Formalism.MainNotions.LiftingTheory.adm23 D HW F)
    (hC4 : Formalism.MainNotions.N.LetterConditionGlobal D HW F) (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l)
    (hg : Loc.Good K 1 LL) [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))] :
    LemmaGs ((HW l).W K 1 LL hg) :=
  lemmaGs_of_lemGAB _ (lemGA_rec D HW F Cm hA l K LL hg) (lemGB_rec D HW F Cm hA h23 hC4 l K LL hg)

theorem wach_basis_lemma_of_admitted (hA : admitted D HW F Cm CR CA CB CK)
    (hGs : ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))], LemmaGs ((HW l).W K 1 LL hg))
    (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
    [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))] : Formalism.MainNotions.N.Pv.LocalLengthBound.ContentBoundLevel ((HW l).W K 1 LL hg) :=
  content_bound_level_of_dcris_exact _ (hA.1 l K 1 LL hg).2.2.2.1 (hA.1 l K 1 LL hg).2.2.2.2.1 (hA.1 l K 1 LL hg).2.2.2.2.2.2.2.2.1
    (fun hCA h11 => (level_tools_of_admitted D HW F Cm hA l K LL (caseA_loc D HW hg hCA)
      (by rw [(D.loc l).PD_p K] at h11; omega)).2)
    (fun hCA h11 c ζ hζ => Formalism.MainNotions.UnusedSlot80.points_exist_of_ring_condition D HW F (gamma_sub_one_in_coordinates D HW F Cm hA) l K LL (caseA_loc D HW hg hCA)
      (by rw [(D.loc l).PD_p K] at h11; omega) c ζ (by rwa [(D.loc l).PD_p K] at hζ))
    (((truncation_clause_of_admitted D HW F Cm hA).2 l K LL hg).2) (Formalism.MainNotions.CrystallineLiftingInputs.Tools.frobenius_power_congruence_of_admitted D HW F Cm hA l K LL hg)
    (hGs l K LL hg) (hA.2.2.2.2.2.2.2.2.2.2.1 l K LL).1 (hA.2.2.2.2.2.2.2.2.2.2.1 l K LL).2.1
    (hA.2.2.2.2.2.2.2.2.2.2.1 l K LL).2.2

theorem frobenius_lift_lemmas_of_admitted (hA : admitted D HW F Cm CR CA CB CK)
    (hH2 : ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))], Formalism.MainNotions.N.Pv.LocalLengthBound.H2Bound ((HW l).W K 1 LL hg))
    (hDN : ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))], LemmaDN ((HW l).W K 1 LL hg))
    (hDN0 : ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))], Formalism.MainNotions.N.Pv.LocalLengthBound.LemmaDN0 ((HW l).W K 1 LL hg))
    (hGs : ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))], LemmaGs ((HW l).W K 1 LL hg)) :
    wachVectorLiftingBoundAtGoodExtensions D HW F := fun l _ K LL hg _ =>
  frobenius_lift_lemmas_general _ (hA.1 l K 1 LL hg).1 (hA.1 l K 1 LL hg).2.2.1 (hA.1 l K 1 LL hg).2.2.2.2.1
    (hA.1 l K 1 LL hg).2.2.2.2.2.2.2.2.1 (hA.2.2.2.2.2.2.2.2.2.2.1 l K LL).1
    (hA.2.2.2.2.2.2.2.2.2.2.1 l K LL).2.1 (hA.2.2.2.2.2.2.2.2.2.2.1 l K LL).2.2 ((Cm l).C K 1 LL hg).tie
    (fun hCA h11 => (level_tools_of_admitted D HW F Cm hA l K LL (caseA_loc D HW hg hCA)
      (by rw [(D.loc l).PD_p K] at h11; omega)).2)
    (fun hCA h11 => Formalism.MainNotions.N.Pv.LocalLengthBound.ptTrans_rec D HW F (gamma_sub_one_in_coordinates D HW F Cm hA) l K LL (caseA_loc D HW hg hCA)
      (by rw [(D.loc l).PD_p K] at h11; omega))
    (hH2 l K LL hg) (wach_basis_lemma_of_admitted D HW F Cm hA hGs l K LL hg) (hDN l K LL hg) (hDN0 l K LL hg)

end Rec

theorem theorem_of_local_lemmas (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CR CA CB CK : ℝ)
    (h12 : admitted D HW F Cm CR CA CB CK → cocyclesToWachVectorsBoundAtGoodExtensions D HW F)
    (h23 : Formalism.MainNotions.LiftingTheory.adm23 D HW F) (hC4 : Formalism.MainNotions.N.LetterConditionGlobal D HW F) :
    Stmt D HW F Cm 25 CR CA CB CK :=
  stmt_of_lemmas D HW F Cm CR CA CB CK fun hA =>
    have hG : ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
        [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))], LemmaGs ((HW l).W K 1 LL hg) :=
      fun l _ K LL hg _ => lemmaGs_rec D HW F Cm hA h23 hC4 l K LL hg
    have hDN : ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
        [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))], LemmaDN ((HW l).W K 1 LL hg) :=
      fun l _ K LL hg _ => Formalism.MainNotions.RamifiedCoefficientChains.S9.bigCellDetWeightedEnergyIntegral.dual_lemma_of_admitted D HW F Cm hA l K LL hg
    have hDN0 := Formalism.MainNotions.RamifiedCoefficientChains.S9.DLev.lemmaDN0_L D HW F Cm hA.1 hA.2.2.2.2.2.2.2.2.2.2.1
    ⟨h12 hA,
      fun l _ K LL hg _ => lattice_bound_three_six_of _
        (frobenius_lift_lemmas_of_admitted D HW F Cm hA (fun l _ K LL hg _ => h2_bound_of_admitted D HW F Cm hA l K LL hg) hDN hDN0 hG
          l K LL hg)
        (Formalism.MainNotions.N.Pv.LocalLengthBound.steps6_of D HW F Cm CR CA CB CK hA hG hDN hDN0 l K LL hg),
      rhoLift_of_Adm D HW F Cm hA⟩

theorem theorem_of_literature_hypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CR CA CB CK : ℝ) (h23 : Formalism.MainNotions.LiftingTheory.adm23 D HW F) (hC4 : Formalism.MainNotions.N.LetterConditionGlobal D HW F)
    (hHerr : Formalism.MainNotions.ElementDenominator.HerrClassNaturalExtension D.loc D.locA HW F) (a22 : Formalism.MainNotions.CrystallineLiftingBounds.adm22 D HW F)
    (hFont : Formalism.MainNotions.InvariantsGenerators.LitFont D HW F) : Stmt D HW F Cm 25 CR CA CB CK :=
  theorem_of_local_lemmas D HW F Cm CR CA CB CK
    (fun hA => Formalism.MainNotions.RamifiedCoefficientChains.S9.LocalLemmasFromLiterature.local_lemmas_of_literature D HW F Cm hA h23 hHerr a22 hFont) h23 hC4

end Formalism.MainNotions.RamifiedCoefficientChains.Asm
end
end
