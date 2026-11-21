import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluingImageCardPowLeDefectGroupCard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasicInequality
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassDefectOrderLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetMassLeAndFinite
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvVolMulPosLeConj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerStabilizersCommensurableVolumeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTermsStatement
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NoLeak
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnessesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFactsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetInFamilyMovedOfNotLeak
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetMoveTermWeightCharacter
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermDoubleCosetMovesFiniteTargetsSplit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianMovesTotalMeasureEstimates
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexMeasureIntegralTransportAndChange
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermDoubleCosetMoveKernelSymm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardEqPowAndIndexGe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmpSqLeCardMulSum

section
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FirstType

theorem geom_le (x : ℝ) (hx : 2 ≤ x) (n : ℕ) : ∑ i ∈ Finset.range (n + 1), x ^ i ≤ 2 * x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have : 0 ≤ x ^ n := by positivity
    nlinarith

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E} {r k : ℕ}

theorem mass_le_sum (S : Frames L r k) (d : S.Datum) (P : Submodule L.O S.V → Prop) {ι : Type}
    (s : Finset ι) (Q : ι → Submodule L.O S.V → Prop)
    (h : ∀ Λ, S.IsTerm d Λ → P Λ → ∃ i ∈ s, Q i Λ) : S.mass d P ≤ ∑ i ∈ s, S.mass d (Q i) := by
  unfold Frames.mass
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine ENNReal.tsum_le_tsum fun o => ?_
  split_ifs with ho
  · obtain ⟨i, hi, hq⟩ := h _ ho.1 ho.2
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) hi)
    rw [if_pos ⟨ho.1, hq⟩]
  · exact zero_le

theorem mass_mono (S : Frames L r k) (d : S.Datum) (P Q : Submodule L.O S.V → Prop)
    (h : ∀ Λ, P Λ → Q Λ) : S.mass d P ≤ S.mass d Q := by
  simpa using mass_le_sum S d P ({()} : Finset Unit) (fun _ => Q) (fun Λ _ hp => ⟨(), by simp, h Λ hp⟩)

theorem first_type_bound : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ β : ℕ, (S.ampSq fun d Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = β) ≤ ENNReal.ofReal (2 * S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * S.Hp ^ (4 * (r + 1))) * (S.q : ℝ) ^ (-((k : ℤ) - 1))) * S.nn := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk β
  have hk1 : 1 ≤ k := by omega
  obtain ⟨hamp, hbasic⟩ := BasicIneq.basic_inequality L r k S hk1
  have hq : 2 ≤ S.q := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
  have hqR : (2 : ℝ) ≤ S.q := by exact_mod_cast hq
  have hH : 0 ≤ S.Hp := by unfold Frames.Hp; positivity
  set A₀ : ℝ := S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) with hA₀
  set A₁ : ℝ := 4 * S.Hp ^ (4 * (r + 1)) with hA₁
  have hA0 : 0 ≤ A₀ := by positivity
  have hA1 : 0 ≤ A₁ := by positivity
  by_cases hex : ∃ d Λ, S.IsTerm d Λ ∧ ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = β
  · obtain ⟨d₀, Λ₀, ht₀, hb₀, -, hβ₀⟩ := hex
    obtain ⟨-, -, -, -, -, ⟨m, -, hm⟩, hiff, -⟩ := Defect.exponents_and_defect L r k S d₀ Λ₀ ht₀
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := by
      rcases m with _ | n
      · exact absurd (hiff.2 (by simpa using hm)) hb₀
      · exact ⟨n, rfl⟩
    have hβ : β = S.q ^ (n + 1) := hβ₀ ▸ hm
    obtain ⟨e, rfl⟩ : ∃ e, k = e + 1 := ⟨k - 1, by omega⟩
    have hx : (2 : ℝ) ≤ (S.q : ℝ) ^ e := by
      have : (S.q : ℝ) ^ 1 ≤ (S.q : ℝ) ^ e := pow_le_pow_right₀ (by linarith) (by omega)
      rw [pow_one] at this
      linarith
    have hmass : ∀ d, S.mass d (fun Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = β) ≤
        ENNReal.ofReal (A₀ * (2 * ((S.q : ℝ) ^ e) ^ n)) := by
      intro d
      refine (mass_le_sum S d _ (Finset.range (n + 1)) (fun i Λ => S.cardI d Λ = S.q ^ i) ?_).trans ?_
      · rintro Λ ht ⟨h1, h2, h3⟩
        obtain ⟨⟨i, hi⟩, -, hle⟩ := SmallImage.small_image L r (e + 1) S d Λ ht
        have h4 := hle h1 h2
        rw [hi, h3, hβ, ← pow_succ'] at h4
        have := (Nat.pow_le_pow_iff_right (by omega)).1 h4
        exact ⟨i, Finset.mem_range.2 (by omega), hi⟩
      · refine (Finset.sum_le_sum fun i _ => (GlobalTheory.T.hermitianDoubleCoset_mass_le_and_finite L r (e + 1) S hk1 d).1 (S.q ^ i)).trans ?_
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ hA0
        refine le_trans (le_of_eq ?_) (geom_le _ hx n)
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Nat.add_sub_cancel, Nat.cast_pow, ← pow_mul, ← pow_mul, mul_comm]
    have h1 := hbasic (fun d Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = β) _ 1 zero_le_one hmass
      (fun d => by simpa using hamp d _)
    have h2 : (S.sumData fun d => S.mass d (fun Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = β)) ≤
        S.sumData fun d => S.mass d fun Λ => S.be d Λ = β := by
      unfold Frames.sumData
      refine ENNReal.tsum_le_tsum fun o => ?_
      gcongr
      exact mass_mono S _ _ _ fun Λ h => h.2.2
    have h3 := GlobalTheory.T.sumData_mass_be_eq_le L r (e + 1) S hk β (by rw [hβ]; exact Nat.one_le_pow _ _ (by omega))
    refine h1.trans ((mul_le_mul_right (h2.trans h3) _).trans (le_of_eq ?_))
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    have hq0 : (S.q : ℝ) ≠ 0 := by positivity
    have : (-(((e + 1 : ℕ) : ℤ) - 1)) = -(e : ℤ) := by push_cast; ring
    rw [this, zpow_neg, zpow_natCast, hβ, Nat.add_sub_cancel, Nat.cast_pow, ← hA₁]
    field_simp
    ring
  · have hmass : ∀ d, S.mass d (fun Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = β) ≤
        ENNReal.ofReal 0 := by
      intro d
      simpa using mass_le_sum S d (fun Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = β)
        (∅ : Finset Unit) (fun _ _ => True) (fun Λ ht hp => absurd ⟨d, Λ, ht, hp⟩ hex)
    have h1 := hbasic (fun d Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = β) _ 1 zero_le_one hmass
      (fun d => by simpa using hamp d _)
    refine h1.trans ?_
    simp

end GlobalTheory.HL.FirstType
end

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFrames_firstType_ampSq_bound : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ β : ℕ, (S.ampSq fun d Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = β) ≤ ENNReal.ofReal (2 * S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * S.Hp ^ (4 * (r + 1))) * (S.q : ℝ) ^ (-((k : ℤ) - 1))) * S.nn := by
  atlas_forward_decl GlobalTheory.HL.FirstType.first_type_bound
end

section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem sum_eq_sum_of_symm_rel {ι : Type*} (Z : Finset ι) (r : ι → ι → Prop)
    (hr : ∀ p q, r p q → r q p) (hne : ∀ p ∈ Z, ∃ q ∈ Z, r p q) (F H : ι → ℂ)
    (hFH : ∀ p ∈ Z, ∀ q ∈ Z, r p q →
      F p * ((Z.filter (r q)).card : ℂ) = H q * ((Z.filter (r p)).card : ℂ)) :
    ∑ p ∈ Z, F p = ∑ p ∈ Z, H p := by
  have hd : ∀ p ∈ Z, ((Z.filter (r p)).card : ℂ) ≠ 0 := by
    intro p hp
    obtain ⟨q, hq, hpq⟩ := hne p hp
    exact_mod_cast (Finset.card_pos.2 ⟨q, Finset.mem_filter.2 ⟨hq, hpq⟩⟩).ne'
  have key : ∀ F : ι → ℂ, ∑ p ∈ Z, F p =
      ∑ p ∈ Z, ∑ q ∈ Z, if r p q then F p / ((Z.filter (r p)).card : ℂ) else 0 := by
    intro F
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀ _ (hd p hp)]
  rw [key F, key H, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun p hp => ?_
  by_cases h : r p q
  · rw [if_pos h, if_pos (hr _ _ h), div_eq_div_iff (hd p hp) (hd q hq), hFH p hp q hq h]
  · rw [if_neg h, if_neg (fun h' => h (hr _ _ h'))]

section
variable {G X : Type} [Group G] [MulAction G X] (St : Subgroup G)

theorem ncard_stabilizer_orbit (y w : X) :
    {w' | ∃ h ∈ St, h • y = y ∧ h • w = w'}.ncard =
      (St ⊓ MulAction.stabilizer G w).relIndex (St ⊓ MulAction.stabilizer G y) := by
  have h1 : {w' | ∃ h ∈ St, h • y = y ∧ h • w = w'} =
      MulAction.orbit (St ⊓ MulAction.stabilizer G y : Subgroup G) w := by
    ext w'
    constructor
    · rintro ⟨h, h1, h2, h3⟩
      exact ⟨⟨h, h1, h2⟩, h3⟩
    · rintro ⟨⟨h, h1, h2⟩, h3⟩
      exact ⟨h, h1, h2, h3⟩
  rw [h1, ← MulAction.index_stabilizer, Subgroup.relIndex]
  congr 1
  ext ⟨h, h1, h2⟩
  simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h3 => ⟨h1, h3⟩, fun h3 => h3.2⟩

theorem relIndex_stabilizer_smul {g : G} (hg : g ∈ St) (y w : X) :
    (St ⊓ MulAction.stabilizer G (g • w)).relIndex (St ⊓ MulAction.stabilizer G (g • y)) =
      (St ⊓ MulAction.stabilizer G w).relIndex (St ⊓ MulAction.stabilizer G y) := by
  rw [← ncard_stabilizer_orbit, ← ncard_stabilizer_orbit,
    ← Set.ncard_image_of_injective {w' | ∃ h ∈ St, h • y = y ∧ h • w = w'} (MulAction.injective g)]
  congr 1
  ext w'
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨h, hh, h1, h2⟩
    refine ⟨_, ⟨g⁻¹ * h * g, St.mul_mem (St.mul_mem (St.inv_mem hg) hh) hg, ?_, rfl⟩, ?_⟩
    · rw [mul_smul, mul_smul, h1, inv_smul_smul]
    · rw [mul_smul, mul_smul, h2, smul_inv_smul]
  · rintro ⟨_, ⟨h, hh, h1, rfl⟩, rfl⟩
    refine ⟨g * h * g⁻¹, St.mul_mem (St.mul_mem hg hh) (St.inv_mem hg), ?_, ?_⟩
    · rw [mul_smul, mul_smul, inv_smul_smul, h1]
    · rw [mul_smul, mul_smul, inv_smul_smul]

theorem invVol_mul_relIndex_comm {G : Type} [Group G] (K0 A B : Subgroup G)
    (hA : K0.relIndex A ≠ 0) (hA' : A.relIndex K0 ≠ 0)
    (hB : K0.relIndex B ≠ 0) (hB' : B.relIndex K0 ≠ 0) :
    invVol K0 A * (B.relIndex A : ℝ) = invVol K0 B * (A.relIndex B : ℝ) := by
  have h1 : K0.relIndex (A ⊓ B) ≠ 0 := fun h =>
    hA (Subgroup.relIndex_eq_zero_of_le_right inf_le_left h)
  have h2 : (A ⊓ B).relIndex K0 ≠ 0 := Subgroup.relIndex_inf_ne_zero hA' hB'
  have e1 := (invVol_mul_pos_le_conj K0 A (A ⊓ B) hA hA' h1 h2).2.2.1 inf_le_left
  have e2 := (invVol_mul_pos_le_conj K0 B (A ⊓ B) hB hB' h1 h2).2.2.1 inf_le_right
  rw [Subgroup.inf_relIndex_left] at e1
  rw [Subgroup.inf_relIndex_right] at e2
  rw [← e1, ← e2]

end

theorem norm_orbit_sum_le_of_symm_kernel : ∀ {G X : Type} [Group G] [MulAction G X] (St K0 : Subgroup G) (P : X → Prop) (om : X → ℂ) (m : X → X → ℝ) (e : ℝ), K0 ≤ St → (∀ h ∈ St, ∀ x, P x → P (h • x) ∧ om (h • x) = om x ∧ invVol K0 (St ⊓ MulAction.stabilizer G (h • x)) = invVol K0 (St ⊓ MulAction.stabilizer G x) ∧ ∀ y, P y → m (h • x) (h • y) = m x y) → (∀ x, P x → K0.relIndex (St ⊓ MulAction.stabilizer G x) ≠ 0 ∧ (St ⊓ MulAction.stabilizer G x).relIndex K0 ≠ 0 ∧ ‖om x‖ = 1 ∧ {y | P y ∧ m x y ≠ 0}.Finite ∧ (∀ y, P y → 0 ≤ m x y ∧ m x y = m y x) ∧ |(∑ᶠ y : {y // P y}, m x y) - 1| ≤ e ∧ ‖∑ᶠ y : {y // P y}, (m x y : ℂ) * om y‖ ≤ e) → {o : MulAction.orbitRel.Quotient St X | P o.out}.Finite → ‖∑' o : MulAction.orbitRel.Quotient St X, if P o.out then ((invVol K0 (St ⊓ MulAction.stabilizer G o.out) : ℝ) : ℂ) * om o.out else 0‖ ≤ 2 * e * ∑' o : MulAction.orbitRel.Quotient St X, if P o.out then invVol K0 (St ⊓ MulAction.stabilizer G o.out) else 0 := by
  intro G X _ _ St K0 P om m e _ hinv hP hfin
  set mu : X → ℝ := fun x => invVol K0 (St ⊓ MulAction.stabilizer G x) with hmu
  have hN : ∀ x, ∃ s : Finset X, P x → ∀ y, y ∈ s ↔ P y ∧ m x y ≠ 0 := by
    intro x
    by_cases hx : P x
    · exact ⟨(hP x hx).2.2.2.1.toFinset, fun _ y => by simp⟩
    · exact ⟨∅, fun h => absurd h hx⟩
  choose N hN using hN
  have hO : ∀ o, o ∈ hfin.toFinset ↔ P o.out := fun o => by simp
  generalize hfin.toFinset = O at hO
  have hR : ∀ x, P x → |(∑ y ∈ N x, m x y) - 1| ≤ e := by
    intro x hx
    have := (hP x hx).2.2.2.2.2.1
    rwa [finsum_subtype_eq_finsum_cond (f := fun y => m x y),
      finsum_cond_eq_sum_of_cond_iff (f := fun y => m x y) (t := N x)] at this
    intro y hy
    rw [hN x hx]
    exact ⟨fun h => ⟨h, hy⟩, fun h => h.1⟩
  have hS : ∀ x, P x → ‖∑ y ∈ N x, (m x y : ℂ) * om y‖ ≤ e := by
    intro x hx
    have := (hP x hx).2.2.2.2.2.2
    rwa [finsum_subtype_eq_finsum_cond (f := fun y => (m x y : ℂ) * om y),
      finsum_cond_eq_sum_of_cond_iff (f := fun y => (m x y : ℂ) * om y) (t := N x)] at this
    intro y hy
    rw [hN x hx]
    refine ⟨fun h => ⟨h, fun h0 => hy ?_⟩, fun h => h.1⟩
    simp [h0]
  have hpos : ∀ x, P x → 0 < mu x := fun x hx =>
    (invVol_mul_pos_le_conj K0 _ _ (hP x hx).1 (hP x hx).2.1 (hP x hx).1 (hP x hx).2.1).2.1
  have t1 : (∑' o : MulAction.orbitRel.Quotient St X,
      if P o.out then ((mu o.out : ℝ) : ℂ) * om o.out else 0) =
      ∑ o ∈ O, ((mu o.out : ℝ) : ℂ) * om o.out := by
    rw [tsum_eq_sum (s := O) (fun o ho => if_neg (fun h => ho ((hO o).2 h)))]
    exact Finset.sum_congr rfl fun o ho => if_pos ((hO o).1 ho)
  have t2 : (∑' o : MulAction.orbitRel.Quotient St X, if P o.out then mu o.out else 0) =
      ∑ o ∈ O, mu o.out := by
    rw [tsum_eq_sum (s := O) (fun o ho => if_neg (fun h => ho ((hO o).2 h)))]
    exact Finset.sum_congr rfl fun o ho => if_pos ((hO o).1 ho)
  refine (congrArg norm t1).trans_le (le_of_le_of_eq ?_ (congrArg (2 * e * ·) t2.symm))
  have huniq : ∀ (o o' : MulAction.orbitRel.Quotient St X) (g : G), g ∈ St →
      g • o.out = o'.out → o = o' := by
    intro o o' g hg h
    rw [← Quotient.out_eq o, ← Quotient.out_eq o']
    exact (Quotient.sound (show MulAction.orbitRel St X o'.out o.out from ⟨⟨g, hg⟩, h⟩)).symm
  have hrep : ∀ z : X, ∃ o : MulAction.orbitRel.Quotient St X, ∃ g ∈ St, g • z = o.out := by
    intro z
    obtain ⟨⟨g, hg⟩, h⟩ : MulAction.orbitRel St X (Quotient.mk _ z).out z := Quotient.mk_out z
    exact ⟨_, g, hg, h⟩
  have unf : ∑ o ∈ O, ∑ z ∈ N o.out, ((mu o.out : ℝ) : ℂ) * ((m o.out z : ℂ) * om z) =
      ∑ o ∈ O, ∑ z ∈ N o.out, ((mu o.out : ℝ) : ℂ) * ((m o.out z : ℂ) * om o.out) := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    set Z := O.sigma fun o => N o.out with hZ
    have mZ : ∀ p, p ∈ Z ↔ P p.1.out ∧ P p.2 ∧ m p.1.out p.2 ≠ 0 := by
      intro p
      rw [hZ, Finset.mem_sigma, hO]
      exact and_congr_right fun h => hN _ h _
    let r : (Σ _ : MulAction.orbitRel.Quotient St X, X) →
        (Σ _ : MulAction.orbitRel.Quotient St X, X) → Prop :=
      fun p q => ∃ g ∈ St, g • p.2 = q.1.out ∧ g • p.1.out = q.2
    have hr : ∀ p q, r p q → r q p := by
      rintro p q ⟨g, hg, h1, h2⟩
      exact ⟨g⁻¹, St.inv_mem hg, by rw [← h2, inv_smul_smul], by rw [← h1, inv_smul_smul]⟩
    have hm : ∀ p ∈ Z, ∀ q, r p q → m q.1.out q.2 = m p.1.out p.2 := by
      rintro p hp q ⟨g, hg, h1, h2⟩
      obtain ⟨a, b, -⟩ := (mZ p).1 hp
      rw [← h1, ← h2, (hinv g hg _ b).2.2.2 _ a, ((hP _ b).2.2.2.2.1 _ a).2]
    have hmem : ∀ p ∈ Z, ∀ q, r p q → q ∈ Z := by
      intro p hp q hpq
      have := hm p hp q hpq
      obtain ⟨g, hg, h1, h2⟩ := hpq
      obtain ⟨a, b, c⟩ := (mZ p).1 hp
      rw [mZ, this, ← h1, ← h2]
      exact ⟨(hinv g hg _ b).1, (hinv g hg _ a).1, c⟩
    have hdeg : ∀ p ∈ Z, ∀ q, r p q → (Z.filter (r p)).card =
        (St ⊓ MulAction.stabilizer G q.2).relIndex (St ⊓ MulAction.stabilizer G q.1.out) := by
      rintro p hp ⟨o, w⟩ ⟨g, hg, h1, h2⟩
      dsimp only at h1 h2 ⊢
      rw [← ncard_stabilizer_orbit, ← Set.ncard_coe_finset,
        ← Set.ncard_image_of_injective _ (sigma_mk_injective (β := fun _ => X) (i := o))]
      congr 1
      ext ⟨o', w'⟩
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Set.mem_image]
      constructor
      · rintro ⟨-, g', hg', h1', h2'⟩
        dsimp only at h1' h2'
        have e1 : (g' * g⁻¹) • o.out = o'.out := by
          rw [← h1, mul_smul, inv_smul_smul, h1']
        have hgg := St.mul_mem hg' (St.inv_mem hg)
        obtain rfl := huniq _ _ _ hgg e1
        refine ⟨w', ⟨_, hgg, e1, ?_⟩, rfl⟩
        rw [← h2, mul_smul, inv_smul_smul, h2']
      · rintro ⟨w'', ⟨h, hh, e1, e2⟩, e3⟩
        rw [← e3]
        have : r p ⟨o, w''⟩ :=
          ⟨h * g, St.mul_mem hh hg, by rw [mul_smul, h1, e1], by rw [mul_smul, h2, e2]⟩
        exact ⟨hmem p hp _ this, this⟩
    refine sum_eq_sum_of_symm_rel Z r hr ?_ _ _ ?_
    · intro p hp
      obtain ⟨o, g, hg, h⟩ := hrep p.2
      have : r p ⟨o, g • p.1.out⟩ := ⟨g, hg, h, rfl⟩
      exact ⟨_, hmem p hp _ this, this⟩
    · intro p hp q hq hpq
      rw [hdeg p hp q hpq, hdeg q hq p (hr _ _ hpq), hm p hp q hpq]
      obtain ⟨g, hg, h1, h2⟩ := hpq
      obtain ⟨a, b, c⟩ := (mZ p).1 hp
      have e1 := invVol_mul_relIndex_comm K0 _ _ (hP _ a).1 (hP _ a).2.1 (hP _ b).1 (hP _ b).2.1
      have e2 := congrArg (fun t : ℝ => (t : ℂ)) e1
      rw [← h1, ← h2, relIndex_stabilizer_smul St hg, (hinv g hg _ b).2.1]
      simp only [hmu]
      rw [(hinv g hg _ b).2.2.1]
      push_cast at e2
      linear_combination (m p.1.out p.2 : ℂ) * om p.2 * e2
  have dec : ∑ o ∈ O, ((mu o.out : ℝ) : ℂ) * om o.out =
      ∑ o ∈ O, ((mu o.out : ℝ) : ℂ) * (∑ z ∈ N o.out, (m o.out z : ℂ) * om z) -
      ∑ o ∈ O, ((mu o.out : ℝ) : ℂ) * om o.out * (((∑ z ∈ N o.out, m o.out z) - 1 : ℝ) : ℂ) := by
    simp only [Finset.mul_sum]
    rw [unf, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    push_cast
    ring
  rw [dec]
  refine (norm_sub_le _ _).trans ?_
  have b1 : ‖∑ o ∈ O, ((mu o.out : ℝ) : ℂ) * (∑ z ∈ N o.out, (m o.out z : ℂ) * om z)‖ ≤
      ∑ o ∈ O, e * mu o.out := by
    refine norm_sum_le_of_le _ fun o ho => ?_
    have h := (hO o).1 ho
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos _ h), mul_comm]
    exact mul_le_mul_of_nonneg_right (hS _ h) (hpos _ h).le
  have b2 : ‖∑ o ∈ O, ((mu o.out : ℝ) : ℂ) * om o.out *
      (((∑ z ∈ N o.out, m o.out z) - 1 : ℝ) : ℂ)‖ ≤ ∑ o ∈ O, e * mu o.out := by
    refine norm_sum_le_of_le _ fun o ho => ?_
    have h := (hO o).1 ho
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (hpos _ h), (hP _ h).2.2.1, mul_one, mul_comm]
    exact mul_le_mul_of_nonneg_right (hR _ h) (hpos _ h).le
  rw [← Finset.mul_sum] at b1 b2
  linarith

end GlobalTheory.HL
end

section
section
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.KernelWeight

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

open scoped Pointwise ENNReal Classical in
open ValuativeRel MeasureTheory in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
theorem _root_.GlobalTheory.HL.KernelWeight.hf_add_left (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (a b y : Fin n → E) :
    _root_.GlobalTheory.HL.hf L Hm (a + b) y =
      _root_.GlobalTheory.HL.hf L Hm a y + _root_.GlobalTheory.HL.hf L Hm b y := by
  have h := _root_.GlobalTheory.HL.DualInter.sub_l L Hm (a + b) b y
  rw [add_sub_cancel_right] at h
  linear_combination -h

open scoped Pointwise ENNReal Classical in
open ValuativeRel MeasureTheory in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
theorem _root_.GlobalTheory.HL.KernelWeight.hf_smul_left (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (c : E) (a y : Fin n → E) :
    _root_.GlobalTheory.HL.hf L Hm (c • a) y = c * _root_.GlobalTheory.HL.hf L Hm a y :=
  _root_.GlobalTheory.HL.DualInter.smul_l L Hm c a y

def hfLin (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (y : Fin n → E) :
    (Fin n → E) →ₗ[E] E where
  toFun x := hf L Hm x y
  map_add' a b := hf_add_left L Hm a b y
  map_smul' c a := hf_smul_left L Hm c a y

theorem exists_coord {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g : Fin (r + 1) → S.V)
    (gs : Fin r → S.V)
    (hd : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (n : S.GLV) (hn : n ∈ S.Nof g) (j : Fin r) (x : S.V) (hx : x ∈ S.spanTo g (j + 1)) :
    ∃ al : Fin (r + 1) → E, x = ∑ i, al i • n (g i) ∧ al j.castSucc = S.h x (gs j) := by
  have hu : n⁻¹ ∈ unipOn (S.spanTo g (j + 1)) (S.spanTo g j) := by
    apply Subgroup.inv_mem
    exact Subgroup.mem_iInf.1 hn.1.2 j
  have h1 : n⁻¹ x ∈ S.spanTo g (j + 1) := (hu.1 x).2 hx
  have h2 : n⁻¹ x - x ∈ S.spanTo g j := hu.2 x hx
  have h3 : n⁻¹ x ∈ Submodule.span E (Set.range g) :=
    Submodule.span_mono (Set.image_subset_range _ _) h1
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 h3
  have h4 : S.spanTo g j ≤ LinearMap.ker (hfLin L S.Hm (gs j)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    have hi' : (i : ℕ) < j := hi
    have : i ≠ j.castSucc := by
      rintro rfl
      simp at hi'
    show hf L S.Hm (g i) (gs j) = 0
    rw [hd, if_neg this]
  have h5 : hfLin L S.Hm (gs j) (n⁻¹ x) = hfLin L S.Hm (gs j) x := by
    have := h4 h2
    rwa [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
  refine ⟨c, ?_, ?_⟩
  · have : x = n (n⁻¹ x) := (n.apply_symm_apply x).symm
    rw [this, ← hc, map_sum]
    simp
  · show _ = hfLin L S.Hm (gs j) x
    rw [← h5, ← hc, map_sum]
    have : ∀ i, hfLin L S.Hm (gs j) (c i • g i) = if i = j.castSucc then c i else 0 := by
      intro i
      rw [map_smul]
      show c i * hf L S.Hm (g i) (gs j) = _
      rw [hd]; split_ifs <;> simp
    simp [this]

end

theorem kernel_weight : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ‖∑ᶠ y : {y // S.IsTerm d y ∧ S.InFF β (j + 1) βJ d y}, (S.kern β (j + 1) βJ d Λ y : ℂ) * S.om d y‖ ≤ 24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk j β βJ d Λ hT hF
  have hW := (GlobalTheory.T.hermitian_double_coset_term_basic_facts L r k S d Λ hT).2.1
  have hom : ‖S.om d Λ‖ = 1 := (GlobalTheory.T.term_invariants_independent_of_witnesses L r k S d Λ _ _ hW).2.2.2.2
  have hchi : ∀ b u, ‖S.chiM j d Λ b u‖ = 1 := fun b u =>
    (GlobalTheory.FramePsi.psi_unitary_character L r k S).2.2.2 _

  have hmove : ∀ w, S.Mv (j + 1) d Λ w → ∃ Λ₁, S.MvTo (j + 1) d Λ Λ₁ w ∧ S.IsTerm d Λ₁ ∧
      S.om d Λ₁ = S.om d Λ * S.chiM j d Λ w.1 w.2.1 := by
    intro w hw
    obtain ⟨Λ₁, h1, h2, -, -, h5⟩ := GlobalTheory.T.hermitianDoubleCoset_move_term_weight_character L r k S j β βJ d Λ hT hF _ _ _ _ hw
    refine ⟨Λ₁, ⟨hw, h1⟩, h2, ?_⟩
    obtain ⟨al, hal, hal1⟩ := exists_coord S S.f S.es S.dual _ hW.2.2.1 j _ hw.1
    obtain ⟨al', hal', hal1'⟩ := exists_coord S S.f' S.es' S.dual' _ hW.2.2.2.1 j _ hw.2.1
    rw [h5 al al' hal hal', hal1, hal1']
    rfl
  have huniq : ∀ w Λ₁ Λ₂, S.MvTo (j + 1) d Λ Λ₁ w → S.MvTo (j + 1) d Λ Λ₂ w → Λ₁ = Λ₂ :=
    fun w Λ₁ Λ₂ h1 h2 => SetLike.coe_injective (h1.2.trans h2.2.symm)
  let P : Submodule L.O S.V → Prop := fun y => S.IsTerm d y ∧ S.InFF β (j + 1) βJ d y
  let G : S.MW → ℂ := fun w => if ∃ Λ₁, S.MvTo (j + 1) d Λ Λ₁ w ∧ P Λ₁ then
    S.om d Λ * S.chiM j d Λ w.1 w.2.1 else 0
  obtain ⟨hGn, hGs⟩ := (GlobalTheory.T.hermDoubleCosetMoves_finite_targets_split L r k S j β βJ d Λ hT hF).2.2.2.2 P (S.om d) G
    (by
      intro w Λ₁ hw
      by_cases hP : P Λ₁
      · obtain ⟨Λ₂, h1, -, h3⟩ := hmove w hw.1
        rw [if_pos hP, huniq w Λ₁ Λ₂ hw h1, h3]
        exact if_pos ⟨Λ₁, hw, hP⟩
      · rw [if_neg hP]
        refine if_neg ?_
        rintro ⟨Λ₂, h1, h2⟩
        exact hP (huniq w Λ₂ Λ₁ h1 hw ▸ h2))
    (by
      intro w hw
      refine if_neg ?_
      rintro ⟨Λ₂, h1, -⟩
      exact hw h1.1)
  obtain ⟨-, hLn, hHn, -, hLb, hHb⟩ := GlobalTheory.T.hermitianMoves_total_measure_estimates L r k S hk j β βJ d Λ hT hF
  obtain ⟨hadd, hsm, -, -⟩ := GlobalTheory.T.indexMeasureIntegral_linear_positive_norm_bound (S.refA (j + 1) Λ)
  set H : S.MW → ℂ := fun w => ind (S.Mv (j + 1) d Λ) w * S.chiM j d Λ w.1 w.2.1 with hH
  obtain ⟨hn2, hc2⟩ := hsm (-S.om d Λ) H hHn
  obtain ⟨hn3, hc3, -⟩ := hadd G _ hGn hn2
  have hb := (hadd _ _ hn3 hLn).2.2 (by
    intro w
    simp only [Pi.add_apply, hH, ind, G]
    by_cases hw : S.Mv (j + 1) d Λ w
    · by_cases hex : ∃ Λ₁, S.MvTo (j + 1) d Λ Λ₁ w ∧ P Λ₁
      · rw [if_pos hex, if_pos hw]
        split_ifs <;> simp
      · have hl : ¬ S.NoLeak Λ w.2.1 := by
          intro hl
          obtain ⟨Λ₁, h1, h2, -⟩ := hmove w hw
          exact hex ⟨Λ₁, h1, h2, GlobalTheory.T.hermitianDoubleCoset_inFamily_moved_of_not_leak L r k S j β βJ d Λ hT hF _ _ _ _ hw hl Λ₁ h1.2⟩
        rw [if_neg hex, if_pos hw, if_pos ⟨hw, hl⟩]
        simp [hom, hchi]
    · have hex : ¬ ∃ Λ₁, S.MvTo (j + 1) d Λ Λ₁ w ∧ P Λ₁ := by
        rintro ⟨Λ₂, h1, -⟩
        exact hw h1.1
      rw [if_neg hex, if_neg hw, if_neg (fun h => hw h.1)]
      simp)
  rw [hc3, hc2] at hb
  have hcK : 0 ≤ S.cK β βJ := by
    unfold Frames.cK
    positivity
  have hG : ‖cint (S.refA (j + 1) Λ) G‖ ≤
      (cint (S.refA (j + 1) Λ) (ind fun w => S.Mv (j + 1) d Λ w ∧ ¬ S.NoLeak Λ w.2.1)).re +
        ‖cint (S.refA (j + 1) Λ) H‖ := by
    have e : cint (S.refA (j + 1) Λ) G =
        (cint (S.refA (j + 1) Λ) G + -S.om d Λ * cint (S.refA (j + 1) Λ) H) +
          S.om d Λ * cint (S.refA (j + 1) Λ) H := by ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add hb ?_)
    rw [norm_mul, hom, one_mul]
  have := mul_le_mul_of_nonneg_left hG hcK
  show ‖∑ᶠ y : {y // P y}, (S.kern β (j + 1) βJ d Λ y : ℂ) * S.om d y‖ ≤ _
  rw [hGs, norm_mul, Complex.norm_real, Real.norm_of_nonneg hcK]
  linarith

end GlobalTheory.HL.KernelWeight
end
end

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianDoubleCoset_kernel_bound_by_weight : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ‖∑ᶠ y : {y // S.IsTerm d y ∧ S.InFF β (j + 1) βJ d y}, (S.kern β (j + 1) βJ d Λ y : ℂ) * S.om d y‖ ≤ 24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
  atlas_forward_decl GlobalTheory.HL.KernelWeight.kernel_weight
end

section
section
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.KernInv

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

def mvEquiv (h : S.GLV) : S.MW ≃+ S.MW :=
  (h.toAddEquiv.prodCongr h.toAddEquiv).prodCongr (h.toAddEquiv.prodCongr (AddEquiv.refl E))

end GlobalTheory.HL.KernInv

namespace GlobalTheory.HL

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma form_apply_apply_of_mem_St {h : S.GLV}
    (hh : h ∈ S.St) (x y : S.V) :
    S.h (h x) (h y) = S.h x y := by
  unfold _root_.GlobalTheory.HL.Frames.St at hh
  have hN := (Subgroup.mem_inf.mp hh).1
  unfold _root_.GlobalTheory.HL.Frames.N _root_.GlobalTheory.HL.Frames.Nof at hN
  have hI := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hN).1).1
  unfold _root_.GlobalTheory.HL.isomG at hI
  unfold _root_.GlobalTheory.HL.Frames.h
  exact hI x y

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma addSubgroup_eq_map_of_apply_mem_iff {M : Type} [AddCommGroup M] (e : M ≃+ M)
    (A B : AddSubgroup M) (hAB : ∀ w, e w ∈ B ↔ w ∈ A) : B = A.map e.toAddMonoidHom := by
  ext w
  constructor
  · intro hw
    exact ⟨e.symm w, (hAB _).mp (by simpa using hw), by simp⟩
  · rintro ⟨w, hw, rfl⟩
    exact (hAB w).mpr hw

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma mem_refB_iff (J : ℕ) (Λ : Submodule L.O S.V) (a b : S.V) :
    (a, b) ∈ S.refB J Λ ↔ a ∈ S.spanTo S.f J ∧ b ∈ S.spanTo S.f' J ∧
      ∃ y ∈ Λ, a + b = (algebraMap F E) S.th • y := by
  unfold _root_.GlobalTheory.HL.Frames.refB
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_prod, AddSubgroup.mem_comap, AddSubgroup.mem_map,
    Submodule.mem_toAddSubgroup, and_assoc]
  exact Iff.rfl.and (Iff.rfl.and (exists_congr fun _ => Iff.rfl.and eq_comm))

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma apply_mem_sup_iff_of_apply_mem_iff (h : S.GLV) (A B : Submodule E S.V)
    (hA : ∀ v, h v ∈ A ↔ v ∈ A) (hB : ∀ v, h v ∈ B ↔ v ∈ B) (v : S.V) :
    h v ∈ A ⊔ B ↔ v ∈ A ⊔ B := by
  simp only [Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, hyz⟩
    refine ⟨h.symm y, (hA _).mp (by simpa using hy), h.symm z, (hB _).mp (by simpa using hz), ?_⟩
    rw [← map_add, hyz, LinearEquiv.symm_apply_apply]
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact ⟨h y, (hA y).mpr hy, h z, (hB z).mpr hz, (map_add h y z).symm⟩

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma apply_mem_perp_Ysp_iff_of_mem_St {h : S.GLV}
    (hh : h ∈ S.St) (J : ℕ) (u : S.V) :
    h u ∈ _root_.GlobalTheory.HL.perp L S.Hm (S.Ysp J) ↔
      u ∈ _root_.GlobalTheory.HL.perp L S.Hm (S.Ysp J) := by
  have hform : ∀ x y, _root_.GlobalTheory.HL.hf L S.Hm (h x) (h y) =
      _root_.GlobalTheory.HL.hf L S.Hm x y := form_apply_apply_of_mem_St S hh
  have hY : ∀ v, h v ∈ S.Ysp J ↔ v ∈ S.Ysp J := by
    unfold _root_.GlobalTheory.HL.Frames.Ysp
    exact apply_mem_sup_iff_of_apply_mem_iff S h _ _
      (_root_.GlobalTheory.FrameAct.spanTo_iff S h hh J)
      (_root_.GlobalTheory.FrameAct.spanTo_iff' S h hh J)
  unfold _root_.GlobalTheory.HL.perp
  show (∀ y ∈ S.Ysp J, _ = 0) ↔ (∀ y ∈ S.Ysp J, _ = 0)
  constructor
  · intro H y hy
    rw [← hform]
    exact H _ ((hY y).mpr hy)
  · intro H y hy
    have hyy : h (h.symm y) = y := h.apply_symm_apply y
    rw [← hyy, hform]
    exact H _ ((hY _).mp (hyy.symm ▸ hy))

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma coe_smul_submodule_eq_iff_of_apply_mem_iff (h : S.GLV) (Λ₁ : Submodule L.O S.V) (P Q : Set S.V)
    (hPQ : ∀ v, h v ∈ Q ↔ v ∈ P) :
    ((h • Λ₁ : Submodule L.O S.V) : Set S.V) = Q ↔ (Λ₁ : Set S.V) = P := by
  simp only [Set.ext_iff, SetLike.mem_coe]
  rw [h.surjective.forall]
  simp only [_root_.GlobalTheory.FrameAct.mem_smul_iff, hPQ]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma eich_apply_apply_of_mem_St {h : S.GLV}
    (hh : h ∈ S.St) (a b v : S.V) (c : E) :
    _root_.GlobalTheory.HL.eich L S.Hm (h a) (h b) c (h v) = h (_root_.GlobalTheory.HL.eich L S.Hm a b c v) := by
  have hform : ∀ x y, _root_.GlobalTheory.HL.hf L S.Hm (h x) (h y) =
      _root_.GlobalTheory.HL.hf L S.Hm x y := form_apply_apply_of_mem_St S hh
  unfold _root_.GlobalTheory.HL.eich
  rw [hform, hform]
  simp only [map_add, map_sub, map_smul]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma apply_mem_moved_smul_iff_of_mem_St {h : S.GLV}
    (hh : h ∈ S.St) (Λ : Submodule L.O S.V) (a b v : S.V) (c : E) :
    h v ∈ S.moved (h • Λ) (h a) (h b) c ↔ v ∈ S.moved Λ a b c := by
  unfold _root_.GlobalTheory.HL.Frames.moved
  show _root_.GlobalTheory.HL.eich L S.Hm (h a) (h b) c (h v) ∈ h • Λ ↔
    _root_.GlobalTheory.HL.eich L S.Hm a b c v ∈ Λ
  rw [eich_apply_apply_of_mem_St S hh, _root_.GlobalTheory.FrameAct.mem_smul_iff]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in

theorem _root_.GlobalTheory.HL.kern_smul_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ (β J βJ : ℕ) (Λ₁ : Submodule L.O S.V), ∀ h ∈ S.St, S.kern β J βJ d (h • Λ) (h • Λ₁) = S.kern β J βJ d Λ Λ₁ := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT β J βJ Λ₁ h hh
  have hform := form_apply_apply_of_mem_St S hh
  have hmove := (_root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d Λ hT h hh).2.2.2.2.2.2.2.2.2.2
  have hA : S.refA J (h • Λ) =
      (S.refA J Λ).map (_root_.GlobalTheory.HL.KernInv.mvEquiv S h).toAddMonoidHom := by
    refine addSubgroup_eq_map_of_apply_mem_iff _ _ _ ?_
    rintro ⟨⟨a, b⟩, u, t⟩
    unfold _root_.GlobalTheory.HL.Frames.refA
    simp only [AddSubgroup.mem_prod]
    change (h a, h b) ∈ S.refB J (h • Λ) ∧ h u ∈ S.refU J (h • Λ) ∧ t ∈ S.refT ↔
      (a, b) ∈ S.refB J Λ ∧ u ∈ S.refU J Λ ∧ t ∈ S.refT
    rw [mem_refB_iff, mem_refB_iff, ← map_add,
      _root_.GlobalTheory.FrameAct.spanTo_iff S h hh,
      _root_.GlobalTheory.FrameAct.spanTo_iff' S h hh]
    have hth := _root_.GlobalTheory.FrameAct.inTh_iff S h Λ (a + b)
    unfold _root_.GlobalTheory.HL.Frames.InTh at hth
    rw [hth]
    unfold _root_.GlobalTheory.HL.Frames.refU
    simp only [AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup,
      _root_.GlobalTheory.FrameAct.mem_smul_iff, apply_mem_perp_Ysp_iff_of_mem_St S hh]
  have hP : ∀ w, _root_.GlobalTheory.IdxInt.ind (S.MvTo J d (h • Λ) (h • Λ₁))
      (_root_.GlobalTheory.HL.KernInv.mvEquiv S h w) = _root_.GlobalTheory.IdxInt.ind (S.MvTo J d Λ Λ₁) w := by
    rintro ⟨⟨a, b⟩, u, t⟩
    have hs : S.sOf ((h a, h b), (h u, t)) = S.sOf ((a, b), (u, t)) := by
      unfold _root_.GlobalTheory.HL.Frames.sOf
      simp only [hform]
    have hiff : S.MvTo J d (h • Λ) (h • Λ₁) ((h a, h b), (h u, t)) ↔
        S.MvTo J d Λ Λ₁ ((a, b), (u, t)) := by
      unfold _root_.GlobalTheory.HL.Frames.MvTo _root_.GlobalTheory.HL.Frames.Mv
      change S.IsMove J d (h • Λ) (h a) (h b) (h u) (S.sOf ((h a, h b), (h u, t))) ∧
          ((h • Λ₁ : Submodule L.O S.V) : Set S.V) =
            S.moved (h • Λ) (h a) (h u) (S.sOf ((h a, h b), (h u, t))) ↔
        S.IsMove J d Λ a b u (S.sOf ((a, b), (u, t))) ∧
          (Λ₁ : Set S.V) = S.moved Λ a u (S.sOf ((a, b), (u, t)))
      rw [hs]
      exact and_congr (hmove J a b u _).symm
        (coe_smul_submodule_eq_iff_of_apply_mem_iff S h Λ₁ _ _ fun v => apply_mem_moved_smul_iff_of_mem_St S hh Λ a u v _)
    unfold _root_.GlobalTheory.IdxInt.ind
    exact if_congr hiff rfl rfl
  unfold _root_.GlobalTheory.HL.Frames.kern
  rw [hA, (_root_.GlobalTheory.IdxInt.Transport.cint_map_and_change.1 _ _ _).2]
  simp only [hP]

end GlobalTheory.HL
end
end

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameMovesKernel_commonStabilizer_smul_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ (β J βJ : ℕ) (Λ₁ : Submodule L.O S.V), ∀ h ∈ S.St, S.kern β J βJ d (h • Λ) (h • Λ₁) = S.kern β J βJ d Λ Λ₁ := by
  atlas_forward_decl GlobalTheory.HL.kern_smul_eq
end

section
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
  [Algebra F E] [TopologicalSpace E] {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ}
  (S : _root_.GlobalTheory.HL.Frames L r k) in
private theorem cK_nonneg' (β βJ : ℕ) :
    0 ≤ S.cK β βJ := by
  unfold _root_.GlobalTheory.HL.Frames.cK
  positivity

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private theorem ind_eq_one_of_pos {W : Type} {P : W → Prop} {w : W} (h : P w) :
    _root_.GlobalTheory.IdxInt.ind P w = 1 := by
  unfold _root_.GlobalTheory.IdxInt.ind
  exact if_pos h

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private theorem ind_eq_zero_of_not {W : Type} {P : W → Prop} {w : W} (h : ¬ P w) :
    _root_.GlobalTheory.IdxInt.ind P w = 0 := by
  unfold _root_.GlobalTheory.IdxInt.ind
  exact if_neg h

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
  [Algebra F E] [TopologicalSpace E] {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ}
  (S : _root_.GlobalTheory.HL.Frames L r k) in
private theorem eq_of_MvTo_of_MvTo {a : ℕ} {d : S.Datum}
    {Λ Λ₁ Λ₂ : Submodule L.O S.V} {w : S.MW}
    (h₁ : S.MvTo a d Λ Λ₁ w) (h₂ : S.MvTo a d Λ Λ₂ w) : Λ₁ = Λ₂ := by
  unfold _root_.GlobalTheory.HL.Frames.MvTo at h₁ h₂
  exact SetLike.coe_injective (h₁.2.trans h₂.2.symm)

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
  [Algebra F E] [TopologicalSpace E] {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ}
  (S : _root_.GlobalTheory.HL.Frames L r k) in
private theorem Mv_of_MvTo {a : ℕ} {d : S.Datum}
    {Λ Λ₁ : Submodule L.O S.V} {w : S.MW}
    (h : S.MvTo a d Λ Λ₁ w) : S.Mv a d Λ w := by
  unfold _root_.GlobalTheory.HL.Frames.MvTo at h
  exact h.1

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
  [Algebra F E] [TopologicalSpace E] {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ}
  (S : _root_.GlobalTheory.HL.Frames L r k) in
private theorem exists_MvTo_isTerm_of_Mv_of_InFF [IsNonarchimedeanLocalField F] [CharZero F]
    (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V)
    (hT : S.IsTerm d Λ) (hF : S.InFF β (j + 1) βJ d Λ)
    (w : S.MW) (hw : S.Mv (j + 1) d Λ w) :
    ∃ Λ₁, S.MvTo (j + 1) d Λ Λ₁ w ∧ S.IsTerm d Λ₁ := by
  have hw' := hw
  unfold _root_.GlobalTheory.HL.Frames.Mv at hw'
  obtain ⟨n₀, -, n₀', -, n'', -, -, -, -, -, hmov, hW⟩ :=
    _root_.GlobalTheory.HL.MoveWit.main L r k S j β βJ d Λ hT hF _ _ _ _ hw'
  refine ⟨n₀⁻¹ • Λ, ?_, ?_⟩
  · unfold _root_.GlobalTheory.HL.Frames.MvTo
    exact ⟨hw, hmov⟩
  · unfold _root_.GlobalTheory.HL.Frames.IsTerm
    exact ⟨⟨_, _⟩, hW⟩

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in

theorem _root_.GlobalTheory.HL.kern_row_sum : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k), 4 * r + 7 ≤ k → ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → |(∑ᶠ y : {y // S.IsTerm d y ∧ S.InFF β (j + 1) βJ d y}, S.kern β (j + 1) βJ d Λ y) - 1| ≤ 24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk j β βJ d Λ hT hF
  obtain ⟨-, -, hfinK, -, hsplit⟩ :=
    _root_.GlobalTheory.HL.moves_split_by_target L r k S j β βJ d Λ hT hF
  obtain ⟨hNMv, hNLeak, -, hI, hIleak, -⟩ :=
    _root_.GlobalTheory.HL.MoveTotal.total_moves L r k S hk j β βJ d Λ hT hF
  have hlin := _root_.GlobalTheory.IdxInt.Lin.main (S.refA (↑j + 1) Λ)
  have hc := cK_nonneg' S β βJ
  set Good : S.MW → Prop := fun w => ∃ Λ₁, S.MvTo (↑j + 1) d Λ Λ₁ w ∧
    (S.IsTerm d Λ₁ ∧ S.InFF β (↑j + 1) βJ d Λ₁) with hGood
  obtain ⟨hNG, hsum⟩ := hsplit
    (fun y => S.IsTerm d y ∧ S.InFF β (↑j + 1) βJ d y)
    (fun _ => 1) (_root_.GlobalTheory.IdxInt.ind Good)
    (fun w Λ₁ h => by
      by_cases hP : S.IsTerm d Λ₁ ∧ S.InFF β (↑j + 1) βJ d Λ₁
      · rw [if_pos hP, ind_eq_one_of_pos ⟨Λ₁, h, hP⟩]
      · rw [if_neg hP, ind_eq_zero_of_not]
        rintro ⟨Λ₂, h₂, hP₂⟩
        exact hP (eq_of_MvTo_of_MvTo S h₂ h ▸ hP₂))
    (fun w hw => ind_eq_zero_of_not fun ⟨Λ₁, h, _⟩ =>
      hw (Mv_of_MvTo S h))
  have hsupp : (Function.support fun y : {y // S.IsTerm d y ∧
      S.InFF β (↑j + 1) βJ d y} =>
        S.kern β (↑j + 1) βJ d Λ ↑y).Finite :=
    (hfinK.preimage Subtype.val_injective.injOn).subset fun y hy => hy
  have hK : (((∑ᶠ y : {y // S.IsTerm d y ∧
      S.InFF β (↑j + 1) βJ d y},
        S.kern β (↑j + 1) βJ d Λ ↑y : ℝ)) : ℂ) =
      (S.cK β βJ : ℂ) *
        _root_.GlobalTheory.IdxInt.cint (S.refA (↑j + 1) Λ)
          (_root_.GlobalTheory.IdxInt.ind Good) := by
    have hmap := map_finsum Complex.ofRealHom hsupp
    simp only [Complex.ofRealHom_eq_coe] at hmap
    rw [hmap, ← hsum]
    simp
  set H : S.MW → ℂ := fun w =>
    _root_.GlobalTheory.IdxInt.ind (S.Mv (↑j + 1) d Λ) w +
      (-1) * _root_.GlobalTheory.IdxInt.ind Good w with hH
  have hNH : _root_.GlobalTheory.IdxInt.Nice (S.refA (↑j + 1) Λ) H :=
    (hlin.1 _ _ hNMv (hlin.2.1 (-1) _ hNG).1).1
  have hIH : _root_.GlobalTheory.IdxInt.cint (S.refA (↑j + 1) Λ) H =
      _root_.GlobalTheory.IdxInt.cint (S.refA (↑j + 1) Λ)
          (_root_.GlobalTheory.IdxInt.ind (S.Mv (↑j + 1) d Λ)) +
        (-1) * _root_.GlobalTheory.IdxInt.cint (S.refA (↑j + 1) Λ)
          (_root_.GlobalTheory.IdxInt.ind Good) := by
    rw [← (hlin.2.1 (-1) _ hNG).2]
    exact (hlin.1 _ _ hNMv (hlin.2.1 (-1) _ hNG).1).2.1
  have hbound : ∀ w, ‖H w‖ ≤ (_root_.GlobalTheory.IdxInt.ind
      (fun w => S.Mv (↑j + 1) d Λ w ∧ ¬ S.NoLeak Λ w.2.1) w).re := by
    intro w
    by_cases hw : S.Mv (↑j + 1) d Λ w
    · by_cases hg : Good w
      · rw [hH]
        simp only
        rw [ind_eq_one_of_pos hw, ind_eq_one_of_pos hg]
        unfold _root_.GlobalTheory.IdxInt.ind
        split_ifs <;> simp
      · have hleak : ¬ S.NoLeak Λ w.2.1 := by
          intro hno
          apply hg
          obtain ⟨Λ₁, h₁, hT₁⟩ := exists_MvTo_isTerm_of_Mv_of_InFF S j β βJ d Λ hT hF w hw
          refine ⟨Λ₁, h₁, hT₁, ?_⟩
          have hw' := hw
          unfold _root_.GlobalTheory.HL.Frames.Mv at hw'
          have h₁' := h₁
          unfold _root_.GlobalTheory.HL.Frames.MvTo at h₁'
          unfold _root_.GlobalTheory.HL.Frames.NoLeak at hno
          exact _root_.GlobalTheory.HL.OffLeak.inFF_moved_of_not_leak L r k S j β βJ d Λ hT hF _ _ _ _
            hw' hno Λ₁ h₁'.2
        rw [hH]
        simp only
        rw [ind_eq_one_of_pos hw, ind_eq_zero_of_not hg, ind_eq_one_of_pos ⟨hw, hleak⟩]
        simp
    · have hg : ¬ Good w := fun ⟨Λ₁, h, _⟩ => hw (Mv_of_MvTo S h)
      rw [hH]
      simp only
      rw [ind_eq_zero_of_not hw, ind_eq_zero_of_not hg]
      unfold _root_.GlobalTheory.IdxInt.ind
      split_ifs <;> simp
  have hnorm := (hlin.1 _ _ hNH hNLeak).2.2 hbound
  have hKre := congrArg Complex.re hK
  rw [Complex.ofReal_re, Complex.re_ofReal_mul] at hKre
  have hsplitre := congrArg Complex.re hIH
  simp only [Complex.add_re, neg_one_mul, Complex.neg_re] at hsplitre
  have hHre : |S.cK β βJ *
      (_root_.GlobalTheory.IdxInt.cint (S.refA (↑j + 1) Λ) H).re| ≤
      16 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
    rw [abs_mul, abs_of_nonneg hc]
    exact (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hc).trans
      ((mul_le_mul_of_nonneg_left hnorm hc).trans hIleak)
  rw [hKre]
  rw [hsplitre] at hHre
  rw [abs_le] at hI hHre ⊢
  constructor <;> nlinarith [hI.1, hI.2, hHre.1, hHre.2]

end GlobalTheory.HL
end

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianDoubleCoset_kernel_row_sum_near_one : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → |(∑ᶠ y : {y // S.IsTerm d y ∧ S.InFF β (j + 1) βJ d y}, S.kern β (j + 1) βJ d Λ y) - 1| ≤ 24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
  atlas_forward_decl GlobalTheory.HL.kern_row_sum
end

section
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem exists_symm_invariant_kernel : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (P : Submodule L.O S.V → Prop), (∀ Λ, P Λ ↔ (S.IsTerm d Λ ∧ S.InFF β (j + 1) βJ d Λ)) → ∃ m : Submodule L.O S.V → Submodule L.O S.V → ℝ, (∀ h ∈ S.St, ∀ x y, P x → P y → m (h • x) (h • y) = m x y) ∧ ∀ x, P x → {y | P y ∧ m x y ≠ 0}.Finite ∧ (∀ y, P y → 0 ≤ m x y ∧ m x y = m y x) ∧ |(∑ᶠ y : {y // P y}, m x y) - 1| ≤ 24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) ∧ ‖∑ᶠ y : {y // P y}, (m x y : ℂ) * S.om d y‖ ≤ 24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk j β βJ d P hP
  have hPe : P = fun Λ => S.IsTerm d Λ ∧ S.InFF β (j + 1) βJ d Λ :=
    funext fun Λ => propext (hP Λ)
  subst hPe
  refine ⟨fun x y => S.kern β (j + 1) βJ d x y, ?_, ?_⟩
  · intro h hh x y hx _
    exact GlobalTheory.T.frameMovesKernel_commonStabilizer_smul_eq L r k S d x hx.1 β (j + 1) βJ y h hh
  · intro x hx
    have base := GlobalTheory.T.hermDoubleCosetMoves_finite_targets_split L r k S j β βJ d x hx.1 hx.2
    refine ⟨?_, ?_, GlobalTheory.T.hermitianDoubleCoset_kernel_row_sum_near_one L r k S hk j β βJ d x hx.1 hx.2,
      GlobalTheory.T.hermitianDoubleCoset_kernel_bound_by_weight L r k S hk j β βJ d x hx.1 hx.2⟩
    · exact base.2.2.1.subset fun y hy => hy.2
    · intro y hy
      exact ⟨base.2.2.2.1 y, GlobalTheory.T.hermDoubleCosetMoveKernel_symm L r k S j β βJ d x hx.1 hx.2 y hy.1 hy.2⟩

end GlobalTheory.HL
end

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symm_invariant_kernel_hermitian_frames : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (P : Submodule L.O S.V → Prop), (∀ Λ, P Λ ↔ (S.IsTerm d Λ ∧ S.InFF β (j + 1) βJ d Λ)) → ∃ m : Submodule L.O S.V → Submodule L.O S.V → ℝ, (∀ h ∈ S.St, ∀ x y, P x → P y → m (h • x) (h • y) = m x y) ∧ ∀ x, P x → {y | P y ∧ m x y ≠ 0}.Finite ∧ (∀ y, P y → 0 ≤ m x y ∧ m x y = m y x) ∧ |(∑ᶠ y : {y // P y}, m x y) - 1| ≤ 24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) ∧ ‖∑ᶠ y : {y // P y}, (m x y : ℂ) * S.om d y‖ ≤ 24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
  atlas_forward_decl GlobalTheory.HL.exists_symm_invariant_kernel
end

section
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.AmpCancel

theorem ofReal_tsum_ite {ι : Type} (p : ι → Prop) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hfin : {i | p i}.Finite) :
    ENNReal.ofReal (∑' i, if p i then f i else 0) =
      ∑' i, if p i then ENNReal.ofReal (f i) else 0 := by
  have hs : ∀ i, i ∉ hfin.toFinset → ¬ p i := fun i hi h => hi (hfin.mem_toFinset.2 h)
  have hs' : ∀ i ∈ hfin.toFinset, p i := fun i hi => hfin.mem_toFinset.1 hi
  rw [tsum_eq_sum (s := hfin.toFinset) (fun i hi => if_neg (hs i hi)),
    tsum_eq_sum (s := hfin.toFinset) (fun i hi => if_neg (hs i hi)),
    Finset.sum_congr rfl (fun i hi => if_pos (hs' i hi)),
    Finset.sum_congr rfl (fun i hi => if_pos (hs' i hi)),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => hf i)]

theorem amp_le_mass {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (hk : 4 * r + 7 ≤ k)
    (β J βJ : ℕ) (d : S.Datum) :
    ENNReal.ofReal (‖S.amp d (S.InFF β J βJ d)‖) ≤
      ENNReal.ofReal (7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3))) * S.mass d (S.InFF β J βJ d) := by
  have hk1 : 1 ≤ k := by omega
  have hc0 : 0 ≤ (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := zpow_nonneg (Nat.cast_nonneg _) _
  have hvol : ∀ K : Subgroup S.GLV, 0 ≤ invVol S.K0 K := fun K =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  obtain ⟨P, hP⟩ : ∃ P : Submodule L.O S.V → Prop, P = fun Λ => S.IsTerm d Λ ∧ S.InFF β J βJ d Λ :=
    ⟨_, rfl⟩
  have hPiff : ∀ Λ, P Λ ↔ S.IsTerm d Λ ∧ S.InFF β J βJ d Λ := fun Λ => by rw [hP]
  have hPfin : {o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V) | P o.out}.Finite :=
    (GlobalTheory.T.hermitianDoubleCoset_mass_le_and_finite L r k S hk1 d).2.subset fun o ho => ((hPiff _).1 ho).1
  have hmass : S.mass d (S.InFF β J βJ d) = ENNReal.ofReal (∑' o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V),
      if P o.out then invVol S.K0 (S.St ⊓ MulAction.stabilizer S.GLV o.out) else 0) := by
    rw [ofReal_tsum_ite (ι := MulAction.orbitRel.Quotient S.St (Submodule L.O S.V)) (fun o => P o.out)
      (fun o => invVol S.K0 (S.St ⊓ MulAction.stabilizer S.GLV o.out)) (fun o => hvol _) hPfin]
    subst hP
    unfold Frames.mass Frames.mu
    exact tsum_congr fun o => by congr
  have hsum0 : 0 ≤ ∑' o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V),
      if P o.out then invVol S.K0 (S.St ⊓ MulAction.stabilizer S.GLV o.out) else 0 :=
    tsum_nonneg fun o => by split_ifs <;> simp [hvol]
  have hamp : S.amp d (S.InFF β J βJ d) = ∑' o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V),
      if P o.out then ((invVol S.K0 (S.St ⊓ MulAction.stabilizer S.GLV o.out) : ℝ) : ℂ) * S.om d o.out
      else 0 := by
    subst hP
    unfold Frames.amp Frames.mu
    exact tsum_congr fun o => by congr
  have key : ‖S.amp d (S.InFF β J βJ d)‖ ≤ 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) *
      ∑' o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V),
        if P o.out then invVol S.K0 (S.St ⊓ MulAction.stabilizer S.GLV o.out) else 0 := by
    by_cases hJ : 1 ≤ J ∧ J ≤ r
    · have hj : ((⟨J - 1, by omega⟩ : Fin r) : ℕ) + 1 = J := by simp only; omega
      obtain ⟨m, hm_inv, hm⟩ := GlobalTheory.T.exists_symm_invariant_kernel_hermitian_frames L r k S hk ⟨J - 1, by omega⟩ β βJ d P
        (fun Λ => by rw [hj]; exact hPiff Λ)
      have hK0 : S.K0 ≤ S.St := fun g hg => hg.1.1
      have bound := GlobalTheory.HL.norm_orbit_sum_le_of_symm_kernel S.St S.K0 P (S.om d) m
        (24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3))) hK0
        (fun h hh x hx => by
          obtain ⟨hT, hI⟩ := (hPiff x).1 hx
          have T := GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms L r k S d x hT h hh
          have hlat := (GlobalTheory.HL.TermBasic.term_basic L r k S d x hT).1.1
          exact ⟨(hPiff _).2 ⟨T.1, (T.2.2.2.2.2.2.2.2.2.1 β J βJ).2 hI⟩, T.2.1,
            ((GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).1 x hlat).2.2 h hh, fun y hy => hm_inv h hh x y hx hy⟩)
        (fun x hx => by
          have hb := GlobalTheory.HL.TermBasic.term_basic L r k S d x ((hPiff x).1 hx).1
          have A := (GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).1 x hb.1.1
          have W := (GlobalTheory.HL.WitIndep.witness_independence L r k S d x _ _ hb.2.1).2.2.2.2
          obtain ⟨h1, h2, h3, h4⟩ := hm x hx
          exact ⟨A.1, A.2.1, W, h1, h2, h3, h4⟩)
        hPfin
      rw [hamp]
      have h2 : 2 * (24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3))) ≤
          7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by linarith
      exact bound.trans (mul_le_mul_of_nonneg_right h2 hsum0)
    · have hempty : ∀ Λ, ¬ P Λ := by
        intro Λ hΛ
        obtain ⟨hT, hTB, -, hle, ⟨y, hy, hyJ⟩, -⟩ := (hPiff Λ).1 hΛ
        by_cases hJr : r < J
        · have := hTB.2.1 y hy
          omega
        · have hJ0 : J = 0 := by omega
          apply hTB.1
          refine le_antisymm (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).2.2.1 fun z hz => ?_
          refine ((GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT).2.2.2.2.2.2.2.2.2.1 z hz).1 ?_
          have := hle z hz
          omega
      rw [hamp]
      simp [hempty]
  rw [hmass, ← ENNReal.ofReal_mul (by linarith)]
  exact ENNReal.ofReal_le_ofReal key

end GlobalTheory.HL.AmpCancel
end

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitude_le_mass_secondType_family : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (β J βJ : ℕ) (d : S.Datum), ENNReal.ofReal (‖S.amp d (S.InFF β J βJ d)‖) ≤ ENNReal.ofReal (7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3))) * S.mass d (S.InFF β J βJ d) := by
  atlas_forward_decl GlobalTheory.HL.AmpCancel.amp_le_mass
end

section
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FamilyBound

theorem geom_le (x : ℝ) (hx : 2 ≤ x) (i : ℕ) : ∑ m ∈ Finset.range (i + 1), x ^ m ≤ 2 * x ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_range_succ]
    have h0 : 0 ≤ x ^ i := by positivity
    have : 2 * x ^ i ≤ x ^ (i + 1) := by rw [pow_succ]; nlinarith
    linarith

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem mass_mono (d : S.Datum) (P Q : Submodule L.O S.V → Prop)
    (h : ∀ Λ, S.IsTerm d Λ → P Λ → Q Λ) : S.mass d P ≤ S.mass d Q := by
  unfold Frames.mass
  refine ENNReal.tsum_le_tsum fun o => ?_
  by_cases ho : S.IsTerm d o.out ∧ P o.out
  · rw [if_pos ho, if_pos ⟨ho.1, h _ ho.1 ho.2⟩]
  · rw [if_neg ho]; exact bot_le

theorem mass_le_sum {ι : Type} (s : Finset ι) (d : S.Datum) (P : Submodule L.O S.V → Prop)
    (Q : ι → Submodule L.O S.V → Prop)
    (h : ∀ Λ, S.IsTerm d Λ → P Λ → ∃ m ∈ s, Q m Λ) : S.mass d P ≤ ∑ m ∈ s, S.mass d (Q m) := by
  unfold Frames.mass
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine ENNReal.tsum_le_tsum fun o => ?_
  by_cases ho : S.IsTerm d o.out ∧ P o.out
  · obtain ⟨m, hm, hq⟩ := h _ ho.1 ho.2
    rw [if_pos ho]
    refine le_trans ?_ (Finset.single_le_sum (f := fun m =>
      if S.IsTerm d o.out ∧ Q m o.out then ENNReal.ofReal (S.mu o.out) else 0) (fun _ _ => bot_le) hm)
    rw [if_pos ⟨ho.1, hq⟩]
  · rw [if_neg ho]; exact bot_le

theorem sumData_mono (φ ψ : S.Datum → ℝ≥0∞) (h : ∀ d, φ d ≤ ψ d) : S.sumData φ ≤ S.sumData ψ := by
  unfold Frames.sumData
  exact ENNReal.tsum_le_tsum fun o => by gcongr; exact h _

end

theorem family_bound : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ β J βJ : ℕ, S.ampSq (S.InFF β J βJ) ≤ ENNReal.ofReal (98 * S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * S.Hp ^ (4 * (r + 1))) * ((S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3))) ^ 2) * S.nn := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk β J βJ
  by_cases hex : ∃ d Λ, S.IsTerm d Λ ∧ S.InFF β J βJ d Λ
  swap
  · have h0 : ∀ d, S.amp d (S.InFF β J βJ d) = 0 := by
      intro d
      unfold Frames.amp
      have : ∀ o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V),
          ¬ (S.IsTerm d o.out ∧ S.InFF β J βJ d o.out) := fun o ho => hex ⟨d, _, ho⟩
      simp [this]
    have : S.ampSq (S.InFF β J βJ) = 0 := by
      unfold Frames.ampSq Frames.sumData
      simp [h0]
    rw [this]; exact bot_le
  obtain ⟨d₀, Λ₀, ht, hF⟩ := hex
  obtain ⟨-, -, -, -, hH, ⟨i, -, hi⟩, hbz, -⟩ := GlobalTheory.HL.Defect.exponents_and_defect L r k S d₀ Λ₀ ht
  have hβ : β = S.q ^ i := by rw [← hF.2.1, hi]
  have hq0 : 0 < S.q := GlobalTheory.HL.SmallImage.resQ_pos S.ϖ S.ϖ_irr
  have hq1 : S.q ≠ 1 := by
    intro h
    exact hF.1.1 (hbz.2 (by rw [hi, h, one_pow]))
  have hq : 2 ≤ S.q := by omega
  have hβ1 : 1 ≤ β := by rw [hβ]; exact Nat.one_le_pow _ _ hq0
  have hk1 : 1 ≤ k := by omega
  set A0 : ℝ := S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) with hA0
  set A1 : ℝ := 4 * S.Hp ^ (4 * (r + 1)) with hA1
  set e : ℝ := (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) with he
  have hA0p : 0 ≤ A0 := by positivity
  have hA1p : 0 ≤ A1 := by positivity
  have hep : 0 ≤ e := by positivity
  have hmass : ∀ d, S.mass d (S.InFF β J βJ d) ≤ ENNReal.ofReal (2 * A0 * (β : ℝ) ^ (k - 1)) := by
    intro d
    refine (mass_le_sum S (Finset.range (i + 1)) d _ (fun m Λ => S.cardI d Λ = S.q ^ m) ?_).trans ?_
    · intro Λ hΛ hP
      obtain ⟨⟨m, hm⟩, hle, -⟩ := GlobalTheory.HL.SmallImage.small_image L r k S d Λ hΛ
      refine ⟨m, ?_, hm⟩
      rw [hm, hP.2.1, hβ] at hle
      have := (Nat.pow_le_pow_iff_right (by omega)).1 hle
      exact Finset.mem_range.2 (by omega)
    · refine (Finset.sum_le_sum fun m _ => (GlobalTheory.T.hermitianDoubleCoset_mass_le_and_finite L r k S hk1 d).1 (S.q ^ m)).trans ?_
      rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ => by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hx : (2 : ℝ) ≤ (S.q : ℝ) ^ (k - 1) := by
        have h2 : (2 : ℝ) ≤ S.q := by exact_mod_cast hq
        exact h2.trans (le_self_pow₀ (by linarith) (by omega))
      have hg := geom_le _ hx i
      have hc : ∀ m : ℕ, ((S.q ^ m : ℕ) : ℝ) ^ (k - 1) = ((S.q : ℝ) ^ (k - 1)) ^ m := by
        intro m; push_cast; rw [← pow_mul, ← pow_mul, mul_comm]
      rw [← Finset.mul_sum, hβ]
      simp only [hc]
      nlinarith [mul_le_mul_of_nonneg_left hg hA0p]
  have h1 := (GlobalTheory.HL.BasicIneq.basic_inequality L r k S hk1).2 (S.InFF β J βJ) _ (7 * e) (by positivity)
    hmass (fun d => GlobalTheory.T.amplitude_le_mass_secondType_family L r k S hk β J βJ d)
  have h2 : (S.sumData fun d => S.mass d (S.InFF β J βJ d)) ≤
      ENNReal.ofReal (A1 * ((β : ℝ) ^ (k - 1))⁻¹) * S.nn :=
    (sumData_mono S _ _ fun d => mass_mono S d _ _ fun Λ _ h => h.2.1).trans (GlobalTheory.T.sumData_mass_be_eq_le L r k S hk β hβ1)
  refine h1.trans ?_
  refine (mul_le_mul_right h2 _).trans ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have hb : (β : ℝ) ^ (k - 1) ≠ 0 := by
    have : (0 : ℝ) < β := by exact_mod_cast hβ1
    positivity
  have : (7 * e) ^ 2 * (2 * A0 * (β : ℝ) ^ (k - 1)) * (A1 * ((β : ℝ) ^ (k - 1))⁻¹) = 98 * A0 * A1 * e ^ 2 := by
    field_simp
    ring
  rw [this]

end GlobalTheory.HL.FamilyBound
end

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianDoubleCoset_secondType_family_ampSq_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ β J βJ : ℕ, S.ampSq (S.InFF β J βJ) ≤ ENNReal.ofReal (98 * S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * S.Hp ^ (4 * (r + 1))) * ((S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3))) ^ 2) * S.nn := by
  atlas_forward_decl GlobalTheory.HL.FamilyBound.family_bound
end

section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.LevelFamilies

theorem relIndex_eq_card_map {O V : Type} [Ring O] [AddCommGroup V] [Module O V]
    (M A : Submodule O V) :
    M.toAddSubgroup.relIndex A.toAddSubgroup = Nat.card (A.map M.mkQ) := by
  have h := AddSubgroup.relIndex_ker A.toAddSubgroup M.mkQ.toAddMonoidHom
  have hk : M.mkQ.toAddMonoidHom.ker = M.toAddSubgroup := by
    ext x
    simp [AddMonoidHom.mem_ker]
  rw [hk] at h
  rw [h]
  rfl

theorem ncard_classes {O V : Type} [Ring O] [AddCommGroup V] [Module O V]
    (M B A : Submodule O V) (hMB : M ≤ B) (hBA : B ≤ A) [Finite (A.map M.mkQ)] :
    Set.ncard {C : Set V | ∃ y ∈ A, y ∉ B ∧ C = {x | x - y ∈ M}} =
      Nat.card (A.map M.mkQ) - Nat.card (B.map M.mkQ) := by
  have hinj : Function.Injective (fun c : V ⧸ M => (M.mkQ ⁻¹' {c} : Set V)) := by
    intro c c' h
    obtain ⟨v, rfl⟩ := M.mkQ_surjective c
    have : v ∈ (M.mkQ ⁻¹' {c'} : Set V) := by
      have h' : (M.mkQ ⁻¹' {M.mkQ v} : Set V) = M.mkQ ⁻¹' {c'} := h
      rw [← h']; simp
    simpa using this
  have hpre : ∀ y : V, (M.mkQ ⁻¹' {M.mkQ y} : Set V) = {x | x - y ∈ M} := by
    intro y
    ext x
    simp [Submodule.Quotient.eq]
  have hmem : ∀ y : V, M.mkQ y ∈ B.map M.mkQ ↔ y ∈ B := by
    intro y
    constructor
    · rintro ⟨b, hb, hby⟩
      have h1 : b - y ∈ M := by simpa [Submodule.Quotient.eq] using hby
      have h2 : y = b - (b - y) := by abel
      rw [h2]
      exact B.sub_mem hb (hMB h1)
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hset : {C : Set V | ∃ y ∈ A, y ∉ B ∧ C = {x | x - y ∈ M}} =
      (fun c : V ⧸ M => (M.mkQ ⁻¹' {c} : Set V)) ''
        ((A.map M.mkQ : Set (V ⧸ M)) \ (B.map M.mkQ : Set (V ⧸ M))) := by
    ext C
    constructor
    · rintro ⟨y, hyA, hyB, rfl⟩
      exact ⟨M.mkQ y, ⟨⟨y, hyA, rfl⟩, fun h => hyB ((hmem y).1 h)⟩, hpre y⟩
    · rintro ⟨c, ⟨⟨y, hyA, rfl⟩, hc⟩, rfl⟩
      exact ⟨y, hyA, fun h => hc ((hmem y).2 h), hpre y⟩
  have hsub : (B.map M.mkQ : Set (V ⧸ M)) ⊆ (A.map M.mkQ : Set (V ⧸ M)) :=
    Submodule.map_mono hBA
  have hfin : (A.map M.mkQ : Set (V ⧸ M)).Finite := Set.toFinite _
  rw [hset, Set.ncard_image_of_injective _ hinj, Set.ncard_diff hsub (hfin.subset hsub)]
  rfl

theorem two_le_resQ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) : 2 ≤ resQ ϖ := by
  have h : Ideal.span {ϖ} = IsLocalRing.maximalIdeal 𝒪[F] := hϖ.maximalIdeal_eq.symm
  have h1 : resQ ϖ = Nat.card (IsLocalRing.ResidueField 𝒪[F]) := by
    unfold resQ
    rw [h]
    rfl
  rw [h1]
  exact Finite.one_lt_card

theorem exists_family : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.TypeBe d Λ → ∃ i J i' : ℕ, 1 ≤ i ∧ (i : ℤ) ≤ S.a ∧ 1 ≤ J ∧ J ≤ r ∧ i' < i ∧ S.InFF (S.q ^ i) J (S.q ^ i - S.q ^ i') d Λ := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT hB
  obtain ⟨-, -, -, -, -, ⟨i, hia, hbe⟩, -, -, -, hlev0, hlev⟩ := GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT
  have hMA : S.M d Λ ≤ S.sat Λ := (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).2.2.1
  have hq : 2 ≤ S.q := two_le_resQ S.ϖ S.ϖ_irr
  have hcard : Nat.card ((S.sat Λ).map (S.M d Λ).mkQ) = S.q ^ i := by
    rw [← hbe, ← relIndex_eq_card_map]; rfl
  haveI hfin : Finite ((S.sat Λ).map (S.M d Λ).mkQ) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard]
    positivity

  let P : ℕ → Prop := fun j => ∃ y ∈ S.sat Λ, S.levC d Λ y = j
  obtain ⟨y0, hy0A, hy0M⟩ : ∃ y ∈ S.sat Λ, y ∉ S.M d Λ := by
    by_contra h
    push_neg at h
    exact hB.1 (le_antisymm hMA h)
  let J := Nat.findGreatest P r
  have hle : ∀ y ∈ S.sat Λ, S.levC d Λ y ≤ J := fun y hy =>
    Nat.le_findGreatest (hB.2.1 y hy) ⟨y, hy, rfl⟩
  have hPJ : P J := Nat.findGreatest_spec (hB.2.1 y0 hy0A) ⟨y0, hy0A, rfl⟩
  have hJr : J ≤ r := Nat.findGreatest_le r
  have hJ1 : 1 ≤ J := by
    have h1 : S.levC d Λ y0 ≠ 0 := fun h => hy0M ((hlev0 y0 hy0A).1 h)
    have := hle y0 hy0A
    omega

  let B : Submodule L.O S.V := S.sat Λ ⊓
    ((S.spanTo S.f (J - 1) ⊔ S.spanTo S.f' (J - 1)).restrictScalars L.O ⊔ S.M d Λ)
  have hBmem : ∀ y ∈ S.sat Λ, y ∈ B ↔ S.levC d Λ y ≤ J - 1 := by
    intro y hy
    rw [hlev y hy]
    constructor
    · rintro ⟨-, h⟩
      obtain ⟨u, hu, m, hm, rfl⟩ := Submodule.mem_sup.1 h
      exact ⟨u, hu, by simpa using hm⟩
    · rintro ⟨u, hu, hm⟩
      exact ⟨hy, Submodule.mem_sup.2 ⟨u, hu, y - u, hm, by abel⟩⟩
  have hMB : S.M d Λ ≤ B := le_inf hMA le_sup_right
  have hBA : B ≤ S.sat Λ := inf_le_left
  have hle' : B.map (S.M d Λ).mkQ ≤ (S.sat Λ).map (S.M d Λ).mkQ := Submodule.map_mono hBA
  haveI hfinB : Finite (B.map (S.M d Λ).mkQ) :=
    Finite.of_injective _ (Submodule.inclusion_injective hle')
  obtain ⟨i', hi'⟩ := (GlobalTheory.FiniteModuleOrder.card_eq_pow_and_index_ge L S.ϖ S.ϖ_irr
    (B.map (S.M d Λ).mkQ)).1
  have hi'q : Nat.card (B.map (S.M d Λ).mkQ) = S.q ^ i' := hi'
  have hn : S.nLev d Λ J = S.q ^ i - S.q ^ i' := by
    rw [← hcard, ← hi'q, ← ncard_classes _ _ _ hMB hBA]
    unfold Frames.nLev
    congr 1
    ext C
    constructor
    · rintro ⟨y, hy, hl, rfl⟩
      refine ⟨y, hy, fun h => ?_, rfl⟩
      have := (hBmem y hy).1 h
      omega
    · rintro ⟨y, hy, hl, rfl⟩
      refine ⟨y, hy, ?_, rfl⟩
      have h1 := hle y hy
      have h2 : ¬ S.levC d Λ y ≤ J - 1 := fun h => hl ((hBmem y hy).2 h)
      omega
  have hlt : S.q ^ i' < S.q ^ i := by
    rw [← hcard, ← hi'q]
    obtain ⟨y, hy, hl⟩ := hPJ
    have hss : (B.map (S.M d Λ).mkQ : Set (S.V ⧸ S.M d Λ)) ⊂
        ((S.sat Λ).map (S.M d Λ).mkQ : Set (S.V ⧸ S.M d Λ)) := by
      refine ⟨hle', fun h => ?_⟩
      obtain ⟨b, hb, hby⟩ := h (⟨y, hy, rfl⟩ : (S.M d Λ).mkQ y ∈ (S.sat Λ).map (S.M d Λ).mkQ)
      have h1 : b - y ∈ S.M d Λ := by simpa [Submodule.Quotient.eq] using hby
      have h2 : y ∈ B := by
        have h3 : y = b - (b - y) := by abel
        rw [h3]
        exact B.sub_mem hb (hMB h1)
      have := (hBmem y hy).1 h2
      omega
    exact Set.ncard_lt_ncard hss (Set.toFinite _)
  have hii : i' < i := (Nat.pow_lt_pow_iff_right (by omega)).1 hlt
  exact ⟨i, J, i', by omega, hia, hJ1, hJr, hii, hB, hbe, hle, hPJ, hn⟩

end GlobalTheory.HL.LevelFamilies
end

section
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.TypesCS

theorem count_le (r a : ℕ) (H : ℝ) (ha : 1 ≤ a) (hH : (2 : ℝ) ^ a ≤ H) :
    ((a + a * (r * a) : ℕ) : ℝ) ≤ H ^ (r + 2) := by
  have hnat : a + a * (r * a) ≤ 2 ^ (a * (r + 2)) := by
    have h1 : a < 2 ^ a := Nat.lt_two_pow_self
    have h2 : r * a < 2 ^ (r * a) := Nat.lt_two_pow_self
    calc a + a * (r * a) = a * (1 + r * a) := by ring
      _ ≤ 2 ^ a * 2 ^ (r * a) := Nat.mul_le_mul h1.le (by omega)
      _ = 2 ^ (a + r * a) := (pow_add 2 a (r * a)).symm
      _ ≤ 2 ^ (a * (r + 2)) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  calc ((a + a * (r * a) : ℕ) : ℝ) ≤ ((2 ^ (a * (r + 2)) : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = ((2 : ℝ) ^ a) ^ (r + 2) := by push_cast; rw [pow_mul]
    _ ≤ H ^ (r + 2) := by gcongr

theorem ampSq_le_of_types : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ B : ℝ≥0∞, (∀ β, (S.ampSq fun d Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = β) ≤ B) → (∀ β J βJ, S.ampSq (S.InFF β J βJ) ≤ B) → (S.ampSq fun d Λ => ¬ S.BBzero d Λ) ≤ ENNReal.ofReal (S.Hp ^ (2 * (r + 2))) * B := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk B hB1 hB2
  have hk1 : 1 ≤ k := by omega
  have hq2 : 2 ≤ S.q := GlobalTheory.HL.LevelFamilies.two_le_resQ S.ϖ S.ϖ_irr
  by_cases hex : ∃ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ
  swap
  ·
    simp only [not_exists] at hex
    have h0 := GlobalTheory.AmpCS.ampSq_le_card_mul_sum L r k S hk1 (∅ : Finset ℕ)
      (fun _ _ _ => False) (fun d Λ => ¬ S.BBzero d Λ)
      (fun d Λ ht => absurd ht (hex d Λ)) (fun d Λ ht => absurd ht (hex d Λ))
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul] at h0
    exact h0.trans zero_le
  obtain ⟨d₀, Λ₀, ht₀⟩ := hex
  obtain ⟨ha0, -, -, hqa, hHp1, -⟩ := GlobalTheory.HL.Defect.exponents_and_defect L r k S d₀ Λ₀ ht₀
  obtain ⟨A, hAa⟩ : ∃ A : ℕ, (A : ℤ) = S.a := ⟨_, Int.toNat_of_nonneg ha0⟩

  let s : Finset (ℕ ⊕ (ℕ × ℕ × ℕ)) :=
    (Finset.Icc 1 A).disjSum
      ((Finset.Icc 1 A ×ˢ Finset.Icc 1 r ×ˢ Finset.range A).filter fun t => t.2.2 < t.1)
  let P : ℕ ⊕ (ℕ × ℕ × ℕ) → S.Datum → Submodule L.O S.V → Prop := fun x =>
    Sum.elim (fun i d Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = S.q ^ i)
      (fun t => S.InFF (S.q ^ t.1) t.2.1 (S.q ^ t.1 - S.q ^ t.2.2)) x
  have hinj : ∀ m n : ℕ, S.q ^ m = S.q ^ n → m = n := fun m n h =>
    Nat.pow_right_injective hq2 h
  have hcover : ∀ d Λ, S.IsTerm d Λ → ((¬ S.BBzero d Λ) ↔ ∃ x ∈ s, P x d Λ) := by
    intro d Λ ht
    obtain ⟨-, -, -, -, -, ⟨i, hia, hbe⟩, hBB, -⟩ :=
      GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ ht
    constructor
    · intro hnz
      have hi1 : 1 ≤ i := by
        rcases Nat.eq_zero_or_pos i with h | h
        · exact absurd (hBB.mpr (by rw [hbe, h, pow_zero])) hnz
        · exact h
      by_cases hT : S.TypeBe d Λ
      · obtain ⟨i₁, J, i', h1, h1a, hJ1, hJr, hi', hF⟩ :=
          GlobalTheory.HL.LevelFamilies.exists_family L r k S d Λ ht hT
        refine ⟨Sum.inr (i₁, J, i'), ?_, hF⟩
        simp only [s, Finset.inr_mem_disjSum, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
          Finset.mem_range]
        omega
      · refine ⟨Sum.inl i, ?_, hnz, hT, hbe⟩
        simp only [s, Finset.inl_mem_disjSum, Finset.mem_Icc]
        omega
    · rintro ⟨x, -, hx⟩
      rcases x with i | ⟨i, J, i'⟩
      · exact hx.1
      · exact hx.1.1
  have hdisj : ∀ d Λ, S.IsTerm d Λ → ∀ x ∈ s, ∀ y ∈ s, P x d Λ → P y d Λ → x = y := by
    intro d Λ _ x hx y hy hPx hPy
    rcases x with i | ⟨i, J, i'⟩ <;> rcases y with j | ⟨j, J', j'⟩ <;>
      dsimp only [P, Sum.elim_inl, Sum.elim_inr] at hPx hPy
    · exact congrArg Sum.inl (hinj _ _ (hPx.2.2.symm.trans hPy.2.2))
    · exact absurd hPy.1 hPx.2.1
    · exact absurd hPx.1 hPy.2.1
    · obtain ⟨-, hb, hle, ⟨y₀, hy₀, hlev⟩, hn⟩ := hPx
      obtain ⟨-, hb', hle', ⟨y₁, hy₁, hlev'⟩, hn'⟩ := hPy
      have hij : i = j := hinj _ _ (hb.symm.trans hb')
      subst hij
      have hJJ : J = J' := le_antisymm (hlev ▸ hle' y₀ hy₀) (hlev' ▸ hle y₁ hy₁)
      subst hJJ
      simp only [s, Finset.inr_mem_disjSum, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_range] at hx hy
      have hlt1 : S.q ^ i' ≤ S.q ^ i := Nat.pow_le_pow_right (by omega) hx.2.le
      have hlt2 : S.q ^ j' ≤ S.q ^ i := Nat.pow_le_pow_right (by omega) hy.2.le
      have hpow : S.q ^ i' = S.q ^ j' := by
        generalize S.q ^ i' = u at hn hlt1
        generalize S.q ^ j' = v at hn' hlt2
        generalize S.q ^ i = w at hn hn' hlt1 hlt2
        omega
      rw [hinj _ _ hpow]
  have hmain := GlobalTheory.AmpCS.ampSq_le_card_mul_sum L r k S hk1 s P (fun d Λ => ¬ S.BBzero d Λ)
    hcover hdisj
  have hsumB : ∑ x ∈ s, S.ampSq (P x) ≤ s.card * B := by
    have hle : ∀ x ∈ s, S.ampSq (P x) ≤ B := by
      intro x _
      rcases x with i | ⟨i, J, i'⟩
      · exact hB1 _
      · exact hB2 _ _ _
    simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul s (fun x => S.ampSq (P x)) B hle
  have hcard : s.card ≤ A + A * (r * A) := by
    simp only [s, Finset.card_disjSum, Nat.card_Icc, Nat.add_sub_cancel]
    have h := Finset.card_filter_le (Finset.Icc 1 A ×ˢ Finset.Icc 1 r ×ˢ Finset.range A)
      (fun t => t.2.2 < t.1)
    simp only [Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel, Finset.card_range] at h
    omega
  have hHp0 : 0 ≤ S.Hp := le_trans zero_le_one hHp1
  have hreal : ((s.card : ℕ) : ℝ) ≤ S.Hp ^ (r + 2) := by
    rcases Nat.eq_zero_or_pos A with hA | hA
    · have : s.card = 0 := by rw [hA] at hcard; simpa using hcard
      rw [this, Nat.cast_zero]
      positivity
    · have h2A : (2 : ℝ) ^ A ≤ S.Hp :=
        calc (2 : ℝ) ^ A ≤ (S.q : ℝ) ^ A := by gcongr; exact_mod_cast hq2
          _ = (S.q : ℝ) ^ S.a := by rw [← hAa, zpow_natCast]
          _ ≤ S.Hp := hqa
      calc ((s.card : ℕ) : ℝ) ≤ ((A + A * (r * A) : ℕ) : ℝ) := by exact_mod_cast hcard
        _ ≤ S.Hp ^ (r + 2) := count_le r A S.Hp hA h2A
  have hN : ((s.card : ℝ≥0∞) * s.card) ≤ ENNReal.ofReal (S.Hp ^ (2 * (r + 2))) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    rw [pow_mul', sq]
    exact mul_le_mul hreal hreal (Nat.cast_nonneg _) (le_trans (Nat.cast_nonneg _) hreal)
  calc (S.ampSq fun d Λ => ¬ S.BBzero d Λ) ≤ s.card * ∑ x ∈ s, S.ampSq (P x) := hmain
    _ ≤ s.card * (s.card * B) := by gcongr
    _ = (s.card * s.card) * B := (mul_assoc _ _ _).symm
    _ ≤ ENNReal.ofReal (S.Hp ^ (2 * (r + 2))) * B := by gcongr

end GlobalTheory.HL.TypesCS
end

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ampSq_le_of_hermitianTermTypes_cauchySchwarz : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ B : ℝ≥0∞, (∀ β, (S.ampSq fun d Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = β) ≤ B) → (∀ β J βJ, S.ampSq (S.InFF β J βJ) ≤ B) → (S.ampSq fun d Λ => ¬ S.BBzero d Λ) ≤ ENNReal.ofReal (S.Hp ^ (2 * (r + 2))) * B := by
  atlas_forward_decl GlobalTheory.HL.TypesCS.ampSq_le_of_types
end

section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.NonzeroDefect

theorem num_first (H q : ℝ) (hq : 2 ≤ q) (hH : 0 ≤ H) (r k : ℕ) :
    2 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * H ^ (4 * (r + 1))) * q ^ (-((k : ℤ) - 1)) ≤
      98 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * H ^ (4 * (r + 1))) * q ^ (-((k : ℤ) - 2 * r - 5)) := by
  have h1 : q ^ (-((k : ℤ) - 1)) ≤ q ^ (-((k : ℤ) - 2 * r - 5)) :=
    zpow_le_zpow_right₀ (by linarith) (by omega)
  have hq0 : 0 < q := by linarith
  gcongr
  norm_num

theorem num_second (H q : ℝ) (hq : 2 ≤ q) (hH : 0 ≤ H) (r k : ℕ) (hk : 4 * r + 7 ≤ k) :
    98 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * H ^ (4 * (r + 1))) *
        (q ^ (1 - ((k : ℤ) - 2 * r - 3))) ^ 2 ≤
      98 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * H ^ (4 * (r + 1))) * q ^ (-((k : ℤ) - 2 * r - 5)) := by
  have hq0 : 0 < q := by linarith
  have h1 : (q ^ (1 - ((k : ℤ) - 2 * r - 3))) ^ 2 ≤ q ^ (-((k : ℤ) - 2 * r - 5)) := by
    rw [← zpow_natCast, ← zpow_mul]
    exact zpow_le_zpow_right₀ (by linarith) (by push_cast; omega)
  gcongr

theorem nonzeroDefect_height_power_absorbs_constants (H : ℝ) (hH : 2 ≤ H) (r : ℕ) :
    H ^ (2 * (r + 2)) * (98 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * H ^ (4 * (r + 1)))) ≤
      H ^ (39 * (r + 1) ^ 2) := by
  have h0 : 0 < H := by linarith
  have h9 : (392 : ℝ) ≤ H ^ 9 := by
    calc (392 : ℝ) ≤ 2 ^ 9 := by norm_num
      _ ≤ H ^ 9 := by gcongr
  calc H ^ (2 * (r + 2)) * (98 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * H ^ (4 * (r + 1))))
      = 392 * (H ^ (2 * (r + 2)) * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * H ^ (4 * (r + 1))) := by ring
    _ ≤ H ^ 9 * (H ^ (2 * (r + 2)) * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * H ^ (4 * (r + 1))) := by gcongr
    _ = H ^ (9 + (2 * (r + 2) + (9 * (r + 1) ^ 2 + 12 * (r + 1)) + 4 * (r + 1))) := by
        simp only [pow_add H]
    _ ≤ H ^ (39 * (r + 1) ^ 2) := pow_le_pow_right₀ (by linarith) (by nlinarith [Nat.zero_le r])

theorem ampSq_nonzero_defect : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → (S.ampSq fun d Λ => ¬ S.BBzero d Λ) ≤ ENNReal.ofReal (S.Hp ^ (39 * (r + 1) ^ 2) * (S.q : ℝ) ^ (-((k : ℤ) - 2 * r - 5))) * S.nn := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk
  by_cases hex : ∃ d Λ, S.IsTerm d Λ ∧ ¬ S.BBzero d Λ
  · obtain ⟨d, Λ, hT, hB⟩ := hex
    have hq : (2 : ℝ) ≤ (S.q : ℝ) := by
      have := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
      exact_mod_cast this
    have hqH : (S.q : ℝ) ≤ S.Hp := (GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ hT).2.2.2.2.2.2.2.1 hB
    have hH : (2 : ℝ) ≤ S.Hp := hq.trans hqH
    have hH0 : (0 : ℝ) ≤ S.Hp := by linarith
    have hq0 : (0 : ℝ) < (S.q : ℝ) := by linarith
    have key := GlobalTheory.T.ampSq_le_of_hermitianTermTypes_cauchySchwarz L r k S hk
      (ENNReal.ofReal (98 * S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * S.Hp ^ (4 * (r + 1))) *
        (S.q : ℝ) ^ (-((k : ℤ) - 2 * r - 5))) * S.nn)
      (fun β => (GlobalTheory.T.hermitianFrames_firstType_ampSq_bound L r k S hk β).trans
        (mul_le_mul_left (ENNReal.ofReal_le_ofReal (num_first _ _ hq hH0 r k)) _))
      (fun β J βJ => (GlobalTheory.T.hermitianDoubleCoset_secondType_family_ampSq_le L r k S hk β J βJ).trans
        (mul_le_mul_left (ENNReal.ofReal_le_ofReal (num_second _ _ hq hH0 r k hk)) _))
    refine key.trans ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_assoc]
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    exact mul_le_mul_of_nonneg_right (nonzeroDefect_height_power_absorbs_constants _ hH r) (by positivity)
  · have h0 : (S.ampSq fun d Λ => ¬ S.BBzero d Λ) = 0 := by
      have ha : ∀ d, S.amp d (fun Λ => ¬ S.BBzero d Λ) = 0 := by
        intro d
        unfold Frames.amp
        have : ∀ Λ, ¬ (S.IsTerm d Λ ∧ ¬ S.BBzero d Λ) := fun Λ h => hex ⟨d, Λ, h⟩
        simp only [this, if_false, tsum_zero]
      unfold Frames.ampSq Frames.sumData
      simp [ha]
    rw [h0]
    exact zero_le

end GlobalTheory.HL.NonzeroDefect
end
