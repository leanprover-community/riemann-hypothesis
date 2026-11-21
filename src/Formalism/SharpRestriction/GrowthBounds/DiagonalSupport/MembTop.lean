import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembDefs
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.DecompositionOfThreeParts
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.LeOfOneLeMul

section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

section Model

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (O : Type) [CommRing O] (K : ℕ) {J : ℕ} (nL : ZMod J → ℕ)

def mlPos : ML J nL r → ZMod J × ℤ
  | ML.ll j l => (j, llPos Fr (segZ j) l.val)
  | ML.lab j m => (j, Fr.fr (segZ j) (r - 1 - m.val))
  | ML.wc j m => (j + 1, Fr.fr (segZ (j + 1) - 1) (r - 1 - m.val))
  | ML.tp j m _ => (j, Fr.fr (segZ j) (r - 1 - m.val))

def tlPos (x : TL J nL r) : ZMod J × ℤ := (x.1, posTL Fr x)

def LSeg (J : ℕ) : Letters (ZMod J × ℤ) := ⟨fun x => decide (Even x.2)⟩

def xiPl (Go : MvPolynomial (ML J nL r × Fin r) O) : MvPolynomial ((ZMod J × ℤ) × Fin r) O :=
  rename (fun v => (mlPos Fr nL v.1, v.2)) Go

def xiNo (No : MvPolynomial (TL J nL r × Fin K) O) : MvPolynomial ((ZMod J × ℤ) × Fin K) O :=
  rename (fun v => (tlPos Fr nL v.1, v.2)) No

def PhiPl (J : ℕ) : MvPolynomial ((ZMod J × ℤ) × Fin r) O →ₐ[O] RRing O n' (r + K) :=
  aeval fun v => X (posOf n' v.1.2, Fin.castAdd K v.2) ^ (p ^ Fr.dist (segZ v.1.1) v.1.2)

def PhiNo (J : ℕ) : MvPolynomial ((ZMod J × ℤ) × Fin K) O →ₐ[O] RRing O n' (r + K) :=
  aeval fun v => X (posOf n' v.1.2, Fin.natAdd r v.2) ^ (p ^ Fr.dist (segZ v.1.1) v.1.2)

def labO [NeZero J] (rho : TL J nL r × Fin (r + K) → ℕ) : Fin n' × Fin (r + K) →₀ ℕ :=
  ∑ x : TL J nL r, ∑ c : Fin (r + K), Finsupp.single (posOf n' (posTL Fr x), c) (rho (x, c))

end Model

def toKK {O : Type} [CommRing O] [IsDomain O] {n' m r K : ℕ} (hk : m + 1 = r + K) (P : RRing O n' (r + K)) :
    MvPolynomial (TV n' (m + 1)) (KK O) :=
  MvPolynomial.map (algebraMap O (KK O)) (rename (castVK hk) P)

structure MFH (p : ℕ) {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (TT : Finset (Fin n')) (L₁ L₂ N₁ G' : ℕ)
    (deg d : Fin n' → ℕ) (Y : ℝ) (k cP : ℕ) : Prop where
  prime : p.Prime
  two_le_r : 2 ≤ r
  frames : FramesOK TT L₁ L₂ N₁ G' Fr
  d_top : ∀ s ∈ Fr.TT, d s = deg s
  d_off : ∀ s, s ∉ Fr.TT → d s = 0
  margin : ∀ j x : ℤ, x ∈ Fr.letters j → ¬ Fr.IsW j x → 128 * (cP : ℝ) ≤ (sl p Fr deg Y k j x : ℝ)

section At

variable (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) (deg : Fin n' → ℕ) (Y : ℝ) (N₁ G' cP : ℕ)
  (d : Fin n' → ℕ) {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ)
  (ka : ZMod J → ℕ → Fin K → ℤ) (rho : TL J Dt.nL r × Fin (r + K) → ℕ)
  (No : MvPolynomial (TL J Dt.nL r × Fin K) O) (Go : MvPolynomial (ML J Dt.nL r × Fin r) O)

def MH : Prop :=
  SignedChainDegreeCondition p O Fr deg Y N₁ G' cP Dt dPl ka ∧ BlockOK Fr p Dt.nL d rho dPl dNo ∧
  NormTest p O cP Dt dNo ka (MvPolynomial.map (algebraMap O (KK O)) No) ∧
  Dt.YY 24 60 (MvPolynomial.map (algebraMap O (KK O)) Go) ∧
  ∀ mo ∈ Go.support, Dt.ph (monomial mo 1) ∈ Pol (KK O) r Dt.d

def Occ (δ : ZMod J × ℤ → ℕ) : Prop := ∃ mo ∈ (xiPl Fr O Dt.nL Go).support, ∀ i, multideg mo i = δ i

def DecAt : Prop :=
  ∀ δ : ZMod J × ℤ → ℕ, Occ p O Fr Dt Go δ →
    ∃ (n : ℕ) (obd : ℤ → ℤ → ℝ) (xi : Fin n → ℤ → SegRing O r K) (dd : ℤ → ℤ → ℕ),
      (∀ (i : Fin n) (j : ℕ), j < Fr.J →
        xi i j ∈ XX' O r K Fr j (fun _ => (mStar p Fr (r + K) N₁ (p ^ G') cP : ℤ))
          (fun x => Bo p Fr deg j x / 2 - sl p Fr deg Y (r + K) j x) (obd j) ∧
        xi i j ∈ restrictSupport O {mm | ∀ x ∈ Fr.letters j, ∑ c : Fin (r + K), mm (x, c) = dd j x}) ∧
      (∀ j : ℕ, j < Fr.J → ∀ x ∈ Fr.letters j, (Fr.IsW j x ∨ x ∈ Fr.LLset j) →
        (dd j x : ℝ) ≤ levDeg p Fr deg j x + levDeg p Fr deg j x / 100) ∧
      ∑ i, ∏ j ∈ Finset.range Fr.J, phSeg O K p Fr (j : ℤ) (xi i j) =
        PhiPl Fr p O K J (homComp δ (xiPl Fr O Dt.nL Go)) * PhiNo Fr p O K J (xiNo Fr O K Dt.nL No)

def AlgAt : Prop :=
  toKK hk (monomial (labO Fr K Dt.nL rho) 1 *
      (PhiPl Fr p O K J (xiPl Fr O Dt.nL Go) * PhiNo Fr p O K J (xiNo Fr O K Dt.nL No))) =
    asm Fr p O hk Dt.nL rho (Dt.ph (MvPolynomial.map (algebraMap O (KK O)) Go))
      (MvPolynomial.map (algebraMap O (KK O)) No)

def DegAt : Prop :=
  ∀ δ : ZMod J × ℤ → ℕ, Occ p O Fr Dt Go δ →
    HasMultideg (toKK hk (monomial (labO Fr K Dt.nL rho) 1 *
      (PhiPl Fr p O K J (homComp δ (xiPl Fr O Dt.nL Go)) * PhiNo Fr p O K J (xiNo Fr O K Dt.nL No)))) d ∧
    ∃ o : ℕ, ∀ mm ∈ (monomial (labO Fr K Dt.nL rho) 1 *
      (PhiPl Fr p O K J (homComp δ (xiPl Fr O Dt.nL Go)) * PhiNo Fr p O K J (xiNo Fr O K Dt.nL No))).support,
      normDeg r mm = o

def LabAt : Prop :=
  IsLabel p Fr (labO Fr K Dt.nL rho) ∧ ∀ v ∈ (labO Fr K Dt.nL rho).support, v.1 ∈ Fr.TT

end At

theorem sum_homComp {R : Type} [CommRing R] {ι : Type} {n : ℕ} (F : MvPolynomial (ι × Fin n) R) :
    ∑ δ ∈ F.support.image (fun mo => fun i => multideg mo i), homComp δ F = F := by
  classical
  conv_rhs => rw [F.as_sum]
  symm
  rw [← Finset.sum_fiberwise_of_maps_to (s := F.support)
    (t := F.support.image (fun mo => fun i => multideg mo i)) (g := fun mo => fun i => multideg mo i)
    (fun mo hmo => Finset.mem_image_of_mem _ hmo)]
  apply Finset.sum_congr rfl
  intro δ _
  unfold homComp
  apply Finset.sum_congr
  · ext mo
    simp only [Finset.mem_filter, funext_iff]
  · intro _ _
    rfl

private theorem mem_range_algebraMap_of_vK_nonneg {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : UniformizedDVR p O) (x : KK O) (h : geQ (vK p x) 0) : x ∈ Set.range (algebraMap O (KK O)) := by
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx, map_zero]⟩
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors O) x
  have hb : (b : O) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  have hbK : algebraMap O (KK O) (b : O) ≠ 0 :=
    fun h0 => hb ((IsFractionRing.injective O (KK O)) (h0.trans (map_zero _).symm))
  have ha : a ≠ 0 := by
    intro ha0
    apply hx
    rw [ha0, map_zero] at hab
    exact (mul_eq_zero.mp hab).resolve_right hbK
  have hord := Formalism.MainNotions.G.Joints.ordW_eq x a b ha hb hab
  have hp0 : IsDiscreteValuationRing.addVal O (p : O) ≠ 0 := by
    rw [Ne, IsDiscreteValuationRing.addVal_eq_zero_iff]
    exact (IsLocalRing.mem_maximalIdeal _).mp S.p_mem
  have hpt : IsDiscreteValuationRing.addVal O (p : O) ≠ ⊤ := by
    rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
    exact S.p_ne
  have hram : 0 < ramE p O := by
    unfold ramE
    rcases ENat.ne_top_iff_exists.mp hpt with ⟨k, hk⟩
    rw [← hk] at hp0 ⊢
    simp only [ENat.toNat_coe]
    exact Nat.pos_of_ne_zero (by exact_mod_cast hp0)
  have hq := h ((((Formalism.MainNotions.G.Joints.nv a : ℤ) - (Formalism.MainNotions.G.Joints.nv (b : O) : ℤ) : ℤ) : ℚ) / (ramE p O : ℚ))
    (by rw [vK, hord, WithTop.map_coe])
  have hq' : (0 : ℚ) ≤ (((Formalism.MainNotions.G.Joints.nv a : ℤ) - (Formalism.MainNotions.G.Joints.nv (b : O) : ℤ) : ℤ) : ℚ) /
      (ramE p O : ℚ) := by exact_mod_cast hq
  have hd : (0 : ℚ) < ramE p O := by exact_mod_cast hram
  have hnum : (0 : ℚ) ≤ (((Formalism.MainNotions.G.Joints.nv a : ℤ) - (Formalism.MainNotions.G.Joints.nv (b : O) : ℤ) : ℤ) : ℚ) :=
    (div_nonneg_iff.mp hq').elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hd))
  have hle : Formalism.MainNotions.G.Joints.nv (b : O) ≤ Formalism.MainNotions.G.Joints.nv a := by
    have : (0 : ℤ) ≤ (Formalism.MainNotions.G.Joints.nv a : ℤ) - (Formalism.MainNotions.G.Joints.nv (b : O) : ℤ) := by exact_mod_cast hnum
    omega
  have hat : IsDiscreteValuationRing.addVal O a ≠ ⊤ := by
    rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact ha
  have hbt : IsDiscreteValuationRing.addVal O (b : O) ≠ ⊤ := by
    rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact hb
  have hvle : IsDiscreteValuationRing.addVal O (b : O) ≤ IsDiscreteValuationRing.addVal O a := by
    rw [← ENat.coe_toNat hat, ← ENat.coe_toNat hbt]
    exact_mod_cast hle
  obtain ⟨c, hc⟩ := IsDiscreteValuationRing.addVal_le_iff_dvd.mp hvle
  refine ⟨c, ?_⟩
  rw [hc, map_mul] at hab
  exact (mul_left_cancel₀ hbK (by rw [← hab, mul_comm])).symm

theorem exists_map_of_coefGe {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : UniformizedDVR p O) {σ : Type} (F : MvPolynomial σ (KK O)) (h : CoefGe p F 0) :
    ∃ Fo : MvPolynomial σ O, MvPolynomial.map (algebraMap O (KK O)) Fo = F := by
  have hrange : F ∈ Set.range (MvPolynomial.map (algebraMap O (KK O))) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro x hx
    obtain ⟨mo, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hx
    exact mem_range_algebraMap_of_vK_nonneg S _ (h mo)
  obtain ⟨Fo, hFo⟩ := hrange
  exact ⟨Fo, hFo⟩

theorem support_of_map {O : Type} [CommRing O] [IsDomain O] {σ : Type} (Fo : MvPolynomial σ O) :
    (MvPolynomial.map (algebraMap O (KK O)) Fo).support = Fo.support := by
  exact MvPolynomial.support_map_of_injective _ (IsFractionRing.injective O (KK O))

theorem membAt_core (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) (deg : Fin n' → ℕ) (Y : ℝ) (N₁ G' cP : ℕ)
    (d : Fin n' → ℕ) {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J)
    (rho : TL J Dt.nL r × Fin (r + K) → ℕ)
    (No : MvPolynomial (TL J Dt.nL r × Fin K) O) (Go : MvPolynomial (ML J Dt.nL r × Fin r) O)
    (hDec : DecAt p O Fr deg Y N₁ G' cP Dt No Go) (hAlg : AlgAt p O hk Fr Dt rho No Go)
    (hDeg : DegAt p O hk Fr d Dt rho No Go) (hLab : LabAt p O Fr Dt rho) :
    ∃ (nq : ℕ) (o : Fin nq → ℕ) (sig : Fin nq → MvPolynomial (TV n' (m + 1)) (KK O)),
      (∀ q, HasMultideg (sig q) d ∧ OneSidedLemma4Element p K O Fr N₁ G' cP deg Y hk (o q) (sig q)) ∧
      ∑ q, sig q = asm Fr p O hk Dt.nL rho (Dt.ph (MvPolynomial.map (algebraMap O (KK O)) Go))
        (MvPolynomial.map (algebraMap O (KK O)) No) := by
  classical
  set S := (xiPl Fr O Dt.nL Go).support.image (fun mo => fun i => multideg mo i) with hS
  have hocc : ∀ δ ∈ S, Occ p O Fr Dt Go δ := by
    intro δ hδ
    obtain ⟨mo, hmo, rfl⟩ := Finset.mem_image.mp hδ
    exact ⟨mo, hmo, fun i => rfl⟩
  let e := S.equivFin
  let δq : Fin S.card → (ZMod J × ℤ → ℕ) := fun q => ((e.symm q : S) : ZMod J × ℤ → ℕ)
  let G : (ZMod J × ℤ → ℕ) → MvPolynomial (Fin n' × Fin (r + K)) O := fun δ =>
    monomial (labO Fr K Dt.nL rho) 1 *
      (PhiPl Fr p O K J (homComp δ (xiPl Fr O Dt.nL Go)) * PhiNo Fr p O K J (xiNo Fr O K Dt.nL No))
  have hoc : ∀ q, Occ p O Fr Dt Go (δq q) := fun q => hocc _ (e.symm q).2
  choose o ho using fun q => (hDeg (δq q) (hoc q)).2
  refine ⟨S.card, o, fun q => toKK hk (G (δq q)), fun q => ⟨(hDeg (δq q) (hoc q)).1, ?_⟩, ?_⟩
  · obtain ⟨n, obd, xi, dd, h1, h2, h3⟩ := hDec (δq q) (hoc q)
    have hmon : monPh O K p Fr (labO Fr K Dt.nL rho) xi = G (δq q) := by
      simp only [monPh, G, h3]
    refine ⟨n, obd, xi, dd, labO Fr K Dt.nL rho, h1, h2, hLab.1, hLab.2, ?_, ?_⟩
    · rw [hmon]
      exact ho q
    · rw [hmon]
      rfl
  · have hAlg' : toKK hk (monomial (labO Fr K Dt.nL rho) 1 *
        (PhiPl Fr p O K J (xiPl Fr O Dt.nL Go) * PhiNo Fr p O K J (xiNo Fr O K Dt.nL No))) =
        asm Fr p O hk Dt.nL rho (Dt.ph (MvPolynomial.map (algebraMap O (KK O)) Go))
          (MvPolynomial.map (algebraMap O (KK O)) No) := hAlg
    rw [← hAlg']
    have hsum : ∑ q, toKK hk (G (δq q)) = ∑ δ ∈ S, toKK hk (G δ) := by
      rw [Equiv.sum_comp e.symm (fun x : S => toKK hk (G x)), Finset.sum_coe_sort S (fun δ => toKK hk (G δ))]
    rw [hsum]
    have e2 : ∑ δ ∈ S, toKK hk (G δ) = toKK hk (∑ δ ∈ S, G δ) := by
      simp only [toKK, map_sum]
    rw [e2]
    congr 1
    simp only [G]
    rw [← Finset.mul_sum, ← Finset.sum_mul, ← map_sum, hS, sum_homComp]

end Formalism.MainNotions.Proposition5Numerics
end
end

section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

def RestDecG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (_S : UniformizedDVR p O) (Fr : Frames n' r) (TT : Finset (Fin n'))
    (L₁ L₂ N₁ G' : ℕ) (deg d : Fin n' → ℕ) (Y : ℝ) (cP : ℕ), MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
      (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (No : MvPolynomial (TL J Dt.nL r × Fin K) O)
      (Go : MvPolynomial (ML J Dt.nL r × Fin r) O),
      MH p O Fr deg Y N₁ G' cP d Dt dPl dNo ka rho No Go → DecAt p O Fr deg Y N₁ G' cP Dt No Go

def RestAlgG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (_S : UniformizedDVR p O) (hk : m + 1 = r + K) (Fr : Frames n' r) (TT : Finset (Fin n'))
    (L₁ L₂ N₁ G' : ℕ) (deg d : Fin n' → ℕ) (Y : ℝ) (cP : ℕ), MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
      (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (No : MvPolynomial (TL J Dt.nL r × Fin K) O)
      (Go : MvPolynomial (ML J Dt.nL r × Fin r) O),
      MH p O Fr deg Y N₁ G' cP d Dt dPl dNo ka rho No Go → AlgAt p O hk Fr Dt rho No Go

def RestDegG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (_S : UniformizedDVR p O) (hk : m + 1 = r + K) (Fr : Frames n' r) (TT : Finset (Fin n'))
    (L₁ L₂ N₁ G' : ℕ) (deg d : Fin n' → ℕ) (Y : ℝ) (cP : ℕ), MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
      (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (No : MvPolynomial (TL J Dt.nL r × Fin K) O)
      (Go : MvPolynomial (ML J Dt.nL r × Fin r) O),
      MH p O Fr deg Y N₁ G' cP d Dt dPl dNo ka rho No Go → DegAt p O hk Fr d Dt rho No Go

def RestLabG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (_S : UniformizedDVR p O) (Fr : Frames n' r) (TT : Finset (Fin n'))
    (L₁ L₂ N₁ G' : ℕ) (deg d : Fin n' → ℕ) (Y : ℝ) (cP : ℕ), MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
      (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (No : MvPolynomial (TL J Dt.nL r × Fin K) O)
      (Go : MvPolynomial (ML J Dt.nL r × Fin r) O),
      MH p O Fr deg Y N₁ G' cP d Dt dPl dNo ka rho No Go → LabAt p O Fr Dt rho

theorem membAt_of (hDec : RestDecG) (hAlg : RestAlgG) (hDeg : RestDegG) (hLab : RestLabG)
    (p : ℕ) [Fact p.Prime] {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (S : UniformizedDVR p O) (hk : m + 1 = r + K) (Fr : Frames n' r) (TT : Finset (Fin n'))
    (L₁ L₂ N₁ G' : ℕ) (deg d : Fin n' → ℕ) (Y : ℝ) (cP : ℕ) (hM : MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP) :
    MembAt p O hk Fr deg Y N₁ G' cP d := by
  intro J _ Dt dPl dNo ka rho N0 hT hB hNT Gp g1 g2 g4
  obtain ⟨Go, rfl⟩ := exists_map_of_coefGe S Gp g1
  obtain ⟨No, rfl⟩ := exists_map_of_coefGe S N0 hNT.1
  have hMH : MH p O Fr deg Y N₁ G' cP d Dt dPl dNo ka rho No Go :=
    ⟨hT, hB, hNT, g2, fun mo hmo => g4 mo (by rw [support_of_map]; exact hmo)⟩
  exact membAt_core p O hk Fr deg Y N₁ G' cP d Dt rho No Go
    (hDec p O S Fr TT L₁ L₂ N₁ G' deg d Y cP hM J Dt dPl dNo ka rho No Go hMH)
    (hAlg p O S hk Fr TT L₁ L₂ N₁ G' deg d Y cP hM J Dt dPl dNo ka rho No Go hMH)
    (hDeg p O S hk Fr TT L₁ L₂ N₁ G' deg d Y cP hM J Dt dPl dNo ka rho No Go hMH)
    (hLab p O S Fr TT L₁ L₂ N₁ G' deg d Y cP hM J Dt dPl dNo ka rho No Go hMH)

theorem margin_real (r : ℕ) (c s : ℝ) (hr : 2 ≤ r) (hc : 0 ≤ c) (h : 100 * (r : ℝ) ^ 2 * c ≤ s) : 128 * c ≤ s := by
  have hr' : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have h4 : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
  have : 400 * c ≤ 100 * (r : ℝ) ^ 2 * c := by nlinarith
  linarith

theorem mfh_of : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → ∀ CLa : ℝ,
    ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ)
    (K : ℕ) [NeZero r] [NeZero K] (_hk : m + 1 = r + K) (F : Frames n' r) (nb : ℕ)
    (B : Fin nb → RRing O n' (r + K)),
    DataII C CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K F nb B →
    MFH p F TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) (flatDeg lam0) (dT TT lam0) Y (r + K)
      (cPrime n' r TT.card c0 cpp cStar) := by
  obtain ⟨C0, hC0, H0⟩ := Formalism.CountingSumsFrames.Top.paramsII0 1 1 le_rfl le_rfl
  refine ⟨max C0 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro C hC CLa p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r hpF _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K _ _
    hk F nb B hD
  obtain ⟨_, H, hF, _, _, _⟩ := hD
  have hC0' : C0 ≤ C := le_trans (le_max_left _ _) hC
  have hC1 : 1 ≤ C := le_trans (le_max_right _ _) hC
  have hB := hyps_basic hC1 H
  have hnb := nb_of hC1 H
  have cg0 := counting_hypotheses_of_hyps hC0 (hyps_mono hC0 hC0' H) 0 (Nat.zero_le _) (Nat.zero_le _)
  obtain ⟨h1, h2, h3, _, h5, _, _, _, _, h10, h11, _⟩ := H
  have ha0 : 0 ≤ a := by linarith [hnb.two_le_a]
  have hfd := fun s hs => flatDeg_bounds (by have := hB.m_ge; omega) ha0 h5 s hs
  have hcPe : ((cPrime n' r TT.card c0 cpp cStar : ℕ) : ℝ) = Formalism.CountingSumsFrames.cPrII r TT.card n' c0 cpp cStar := by
    unfold cPrime Formalism.CountingSumsFrames.cPrII Formalism.CountingSumsFrames.omII
    push_cast
    ring
  rw [hk] at cg0
  have A0 := (H0 p r TT.card (orbitWindowCount r de h x) 0 1 (r + K) n' L₁ (goodG' r de h x) Y a 0 c0 cpp Dp cStar cg0
    le_rfl (by unfold Formalism.CountingSumsFrames.QII; positivity)).2.1
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  refine ⟨hpF.out, h2, hF, ?_, ?_, ?_⟩
  · intro s hs
    rw [hF.1] at hs
    unfold dT
    rw [if_pos hs]
  · intro s hs
    rw [hF.1] at hs
    unfold dT
    rw [if_neg hs]
  · intro jj xx hx hW
    have hBo := Bo_ge hF.2.1 (by omega) p (by omega) (flatDeg lam0) a
      (fun s hs => (hfd s (by rw [hF.1] at hs; exact hs)).1) jj xx hx hW
    have hE : (F.fr jj (r - 1) - F.fr (jj - 1) 0).toNat ≤ goodG' r de h x := by
      have := hF.2.2.1 jj
      omega
    have hq : a / Formalism.CountingSumsFrames.QII p (goodG' r de h x) ≤ Bo p F (flatDeg lam0) jj xx := by
      refine le_trans ?_ hBo
      apply div_le_div_of_nonneg_left ha0 (by positivity)
      exact pow_le_pow_right₀ hp1 hE
    have q := (A0 _ hq).1
    have n1 : 0 ≤ 24 * (((orbitWindowCount r de h x : ℕ) : ℝ) + r) * c0 := by positivity
    have n2 : 0 ≤ Formalism.CountingSumsFrames.mStarII (orbitWindowCount r de h x) (r + K) (Formalism.CountingSumsFrames.QII p (goodG' r de h x))
        (Formalism.CountingSumsFrames.cPrII r TT.card n' c0 cpp cStar) 0 := by
      unfold Formalism.CountingSumsFrames.mStarII Formalism.CountingSumsFrames.cPrII Formalism.CountingSumsFrames.omII Formalism.CountingSumsFrames.QII
      positivity
    have q2 : 100 * (r : ℝ) ^ 2 * ((cPrime n' r TT.card c0 cpp cStar : ℕ) : ℝ) ≤
        (sl p F (flatDeg lam0) Y (r + K) jj xx : ℝ) := by
      rw [hcPe]
      have e : (sl p F (flatDeg lam0) Y (r + K) jj xx : ℝ) =
          Formalism.CountingSumsFrames.slII Y (r + K) (Bo p F (flatDeg lam0) jj xx) := rfl
      rw [e]
      linarith
    exact margin_real r _ _ h2 (Nat.cast_nonneg _) q2

theorem membership_of_four_parts (hDec : RestDecG) (hAlg : RestAlgG) (hDeg : RestDegG) (hLab : RestLabG)
    (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : RestMemb D CLa Ck Crk Cdeg := by
  intro _
  obtain ⟨C₁, h1, h2⟩ := mfh_of
  refine ⟨C₁, h1, fun C hC => ?_⟩
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K _ _
    hk F nb B hD
  exact membAt_of hDec hAlg hDeg hLab p O (dvrOfStd hD.1) hk F TT L₁ L₂ _ _ _ _ Y _
    (h2 C hC CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K hk F nb B hD)

end Formalism.MainNotions.Proposition5Numerics
end
end
