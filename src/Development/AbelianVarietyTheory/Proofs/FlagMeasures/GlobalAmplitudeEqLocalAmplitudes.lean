import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Equality
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordinateLatticeUniqueTermAlmostAllPlacesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianAmplitudeMassProductStructure
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDatumEquivariantFlagIsometriesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsOrbitsHeightsAmplitudesInCoordinates
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometryStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.AutLzFiniteOfLoop
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedTermLatticeIsGlobalTermPhase
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TsumOrbitNormaliser

section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.BadPlaces

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E} {r k : ℕ} (S : Frames L r k)

end Local

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : _root_.Formalism.MainNotions.S.Loc.LocE F E}
  {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma two_le_q' : 2 ≤ S.q := by
  unfold _root_.GlobalTheory.HL.Frames.q _root_.GlobalTheory.HL.resQ
  rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer S.ϖ).1
    S.ϖ_irr]
  show 2 ≤ Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation F).integer)
  exact Finite.one_lt_card_iff_nontrivial.2 inferInstance

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : _root_.Formalism.MainNotions.S.Loc.LocE F E}
  {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma q_le_Hp_of_Hp_ne_one {d : S.Datum} {Λ : Submodule L.O S.V}
    (h : S.IsTerm d Λ) (hne : S.Hp ≠ 1) :
    (S.q : ℝ) ≤ S.Hp := by
  have hq : (2 : ℝ) ≤ S.q := by
    exact_mod_cast two_le_q' S
  have h1 : 1 ≤ S.Hp :=
    (_root_.GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ h).2.2.2.2.1
  have hH : S.Hp = (S.q : ℝ) ^
      (S.vth + S.a + S.vD) := rfl
  rcases le_or_gt (S.vth + S.a + S.vD) 0
    with hn | hn
  · exact absurd (le_antisymm (hH ▸ zpow_le_one_of_nonpos₀ (by linarith) hn) h1) hne
  · rw [hH]
    calc (S.q : ℝ)
        = (S.q : ℝ) ^ (1 : ℤ) := (zpow_one _).symm
      _ ≤ _ := zpow_le_zpow_right₀ (by linarith) (by omega)

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : _root_.Formalism.MainNotions.S.Loc.LocE F E}
  {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma vE_nonneg_of_mem_O (ϖ : (ValuativeRel.valuation F).integer) {x : E}
    (hx : x ∈ L.O) : 0 ≤ _root_.GlobalTheory.HL.vE L ϖ x := by
  unfold _root_.GlobalTheory.HL.vE
  have hmem : (0 : ℤ) ∈ {m : ℤ | ∃ y ∈ L.O, x = algebraMap F E ((ϖ : F) ^ m) * y} :=
    ⟨x, hx, by simp⟩
  by_cases hb : BddAbove {m : ℤ | ∃ y ∈ L.O, x = algebraMap F E ((ϖ : F) ^ m) * y}
  · exact le_csSup hb hmem
  · rw [Int.csSup_of_not_bddAbove hb]

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : _root_.Formalism.MainNotions.S.Loc.LocE F E}
  {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma gg_false_and_vE_eq_zero_of_Hp_eq_one {d : S.Datum} {Λ : Submodule L.O S.V}
    (h : S.IsTerm d Λ) (h1 : S.Hp = 1) :
    S.gg = false ∧
      _root_.GlobalTheory.HL.vE L S.ϖ S.G = 0 ∧
      ∀ l, S.D l ≠ 0 →
        _root_.GlobalTheory.HL.vE L S.ϖ
          (S.D l * L.cj (S.D l)) = 0 := by
  obtain ⟨ha, hvD, hD, -⟩ := _root_.GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ h
  have hq2 := two_le_q' S
  have hq : (1 : ℝ) < S.q := by exact_mod_cast (by omega : 1 < S.q)
  have hn : S.vth + S.a + S.vD = 0 := by
    have hpow : (S.q : ℝ) ^
        (S.vth + S.a + S.vD) =
        (S.q : ℝ) ^ (0 : ℤ) := by
      rw [zpow_zero]; exact h1
    exact zpow_right_injective₀ (by linarith) hq.ne' hpow
  have hth : 0 ≤ S.vth := by
    unfold _root_.GlobalTheory.HL.Frames.vth; split_ifs <;> norm_num
  have hth0 : S.vth = 0 := by omega
  have ha0 : S.a = 0 := by omega
  have hvD0 : S.vD = 0 := by omega
  refine ⟨?_, ?_, ?_⟩
  · cases hg : S.gg
    · rfl
    · simp [_root_.GlobalTheory.HL.Frames.vth, hg] at hth0
  · have h2 := ha0
    unfold _root_.GlobalTheory.HL.Frames.a at h2
    rw [hth0] at h2
    simpa using h2
  · intro l hl
    by_cases hl0 : l = 0
    · subst hl0
      have hD0 : S.D 0 = 1 := by
        simp [_root_.GlobalTheory.HL.Frames.D, _root_.GlobalTheory.HL.lead]
      rw [hD0, map_one, one_mul]
      simpa using _root_.GlobalTheory.UnramVal.vE_zpow_mul_unit L S.ϖ_irr 0 1
    · have hsum := hvD0
      unfold _root_.GlobalTheory.HL.Frames.vD at hsum
      rw [Finset.sum_eq_zero_iff_of_nonneg] at hsum
      · simpa [hl0, hl] using hsum l (Finset.mem_univ _)
      · intro i _
        split_ifs
        · exact vE_nonneg_of_mem_O _
            (L.O.mul_mem (hD i) (_root_.GlobalTheory.HL.Inhab.cj_int L (hD i)))
        · exact le_rfl

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : _root_.Formalism.MainNotions.S.Loc.LocE F E}
  {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma exists_inv_mem_O_of_vE_mul_cj_eq_zero (ϖ : (ValuativeRel.valuation F).integer)
    (hϖ : Irreducible ϖ) {x : E} (hx : x ∈ L.O) (hxu : IsUnit x)
    (hv : _root_.GlobalTheory.HL.vE L ϖ (x * L.cj x) = 0) : ∃ y ∈ L.O, x * y = 1 := by
  haveI := _root_.GlobalTheory.HL.Model.nontrivial L
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.UnramOrder.exists_norm L hx
  have hc0 : (c : F) ≠ 0 := by
    intro h0
    have hu : IsUnit (x * L.cj x) := hxu.mul (hxu.map L.cj)
    rw [hc, h0, map_zero] at hu
    exact not_isUnit_zero hu
  obtain ⟨m, u, hmu⟩ := _root_.GlobalTheory.UnramVal.exists_eq_zpow_mul_unit hϖ hc0
  have hm : m = 0 := by
    have hval := _root_.GlobalTheory.UnramVal.vE_zpow_mul_unit L hϖ m u
    rw [← hmu, ← hc, hv] at hval
    exact hval.symm
  subst hm
  have hu1 : ((u : (ValuativeRel.valuation F).integer) : F) *
      ((u⁻¹ : (ValuativeRel.valuation F).integerˣ) : (ValuativeRel.valuation F).integer) = 1 := by
    exact_mod_cast congrArg (fun z : (ValuativeRel.valuation F).integer => (z : F)) u.mul_inv
  refine ⟨L.cj x * algebraMap F E
      (((u⁻¹ : (ValuativeRel.valuation F).integerˣ) : (ValuativeRel.valuation F).integer) : F),
    L.O.mul_mem (_root_.GlobalTheory.HL.Inhab.cj_int L hx) ((_root_.GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (Subtype.prop _)), ?_⟩
  rw [← mul_assoc, hc, ← map_mul, hmu, zpow_zero, one_mul, hu1, map_one]

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : _root_.Formalism.MainNotions.S.Loc.LocE F E}
  {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma norm_amp_BBzero_eq_one_and_mass_eq_one_of_Hp_eq_one (hk : 4 * r + 7 ≤ k) {d : S.Datum}
    {Λ : Submodule L.O S.V} (h : S.IsTerm d Λ) (h1 : S.Hp = 1) (d' : S.Datum)
    (hd' : ∃ Λ', S.IsTerm d' Λ') :
    ‖S.amp d' (S.BBzero d')‖ = 1 ∧
      S.mass d' (fun _ => True) = 1 := by
  obtain ⟨hgg, hG, hDl⟩ := gg_false_and_vE_eq_zero_of_Hp_eq_one S h h1
  obtain ⟨hBB, -, -, hmass01⟩ := _root_.GlobalTheory.HL.GoodPlace.equality L r k S hk hgg hG hDl
  have ha : S.a = 0 := by
    simp [_root_.GlobalTheory.HL.Frames.a, _root_.GlobalTheory.HL.Frames.vth,
      hgg, hG]
  have hDO := (_root_.GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ h).2.2.1
  have hunit : ∀ l, S.D l ≠ 0 → S.D l ∈ L.O ∧
      ∃ y ∈ L.O, S.D l * y = 1 := fun l hl =>
    ⟨hDO l, exists_inv_mem_O_of_vE_mul_cj_eq_zero S.ϖ
      S.ϖ_irr (hDO l)
      ((_root_.GlobalTheory.FrameBasic.main L r k S).2.2.2.2.1 l hl) (hDl l hl)⟩
  have hcls : ∃ C0, ∀ C, S.IsIntCls C →
      ∃ g ∈ S.St, C = g • C0 :=
    ⟨_, (_root_.GlobalTheory.HL.GoodClass.one_class L r k S hgg hunit).2.2⟩
  obtain ⟨C0, hcls⟩ := hcls
  obtain ⟨Λ', hΛ'⟩ := hd'
  have hexists : ∀ C, S.IsIntCls C → ∃ Λ0, S.IsTerm d' Λ0 ∧
      S.Fr d' Λ0 = C ∧ ∃ g ∈ S.St, Λ0 = g • Λ' := by
    intro C hC
    obtain ⟨g2, hg2, rfl⟩ := hcls C hC
    obtain ⟨g1, hg1, he1⟩ :=
      hcls _ (_root_.GlobalTheory.HL.TermBasic.term_basic L r k S d' Λ' hΛ').2.2.2.2.2.2.1
    have hg : g2 * g1⁻¹ ∈ S.St := mul_mem hg2 (inv_mem hg1)
    have hact := _root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d' Λ' hΛ' _ hg
    refine ⟨(g2 * g1⁻¹) • Λ', hact.1, ?_, _, hg, rfl⟩
    rw [hact.2.2.2.2.1, he1, smul_smul, inv_mul_cancel_right]
  have horbit : ∀ Λ2, S.IsTerm d' Λ2 → ∃ g ∈ S.St, Λ2 = g • Λ' := by
    intro Λ2 h2
    obtain ⟨Λ0, hT0, hF0, hg⟩ :=
      hexists _ (_root_.GlobalTheory.HL.TermBasic.term_basic L r k S d' Λ2 h2).2.2.2.2.2.2.1
    rw [← (_root_.GlobalTheory.HL.UnimodTerm.term_unique L r k S d' Λ2 h2 ha).2 Λ0 hT0 hF0]
    exact hg
  set o0 : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V) :=
    Quotient.mk (MulAction.orbitRel S.St (Submodule L.O S.V)) Λ' with ho0
  have hne : ∀ o, o ≠ o0 → ¬ S.IsTerm d' (Quotient.out o) := by
    intro o ho hT
    obtain ⟨g, hg, he⟩ := horbit _ hT
    have hq : Quotient.mk (MulAction.orbitRel S.St (Submodule L.O S.V))
        (Quotient.out o) = o0 := by
      rw [he]; exact Quotient.sound ⟨⟨g, hg⟩, rfl⟩
    exact ho ((Quotient.out_eq o).symm.trans hq)
  obtain ⟨m, hm⟩ := Quotient.exact (Quotient.out_eq o0)
  have hT2 : S.IsTerm d' (Quotient.out o0) := by
    rw [← hm]; exact (_root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d' Λ' hΛ' _ m.2).1
  have hmass : S.mass d' (fun _ => True) =
      ENNReal.ofReal (S.mu (Quotient.out o0)) := by
    unfold _root_.GlobalTheory.HL.Frames.mass
    rw [tsum_eq_single o0]
    · rw [if_pos ⟨hT2, trivial⟩]
    · intro o ho
      rw [if_neg]
      exact fun hc => hne o ho hc.1
  have hpos : 0 < S.mu (Quotient.out o0) := by
    obtain ⟨hA, hB, -⟩ := (_root_.GlobalTheory.HL.volSt L r k S).1 _
      (_root_.GlobalTheory.HL.TermBasic.term_basic L r k S d' _ hT2).1.1
    unfold _root_.GlobalTheory.HL.Frames.mu _root_.GlobalTheory.HL.invVol
    exact div_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hB)) (Nat.cast_pos.2 (Nat.pos_of_ne_zero hA))
  have hmass1 : S.mass d' (fun _ => True) = 1 := by
    rcases hmass01 d' with h0 | h0
    · rw [hmass, ENNReal.ofReal_eq_zero] at h0
      exact absurd h0 (not_le.2 hpos)
    · exact h0
  have hmu : S.mu (Quotient.out o0) = 1 := by
    rw [hmass1, eq_comm, ENNReal.ofReal_eq_one] at hmass
    exact hmass
  refine ⟨?_, hmass1⟩
  unfold _root_.GlobalTheory.HL.Frames.amp
  rw [tsum_eq_single o0]
  swap
  · intro o ho
    rw [if_neg]
    exact fun hc => hne o ho hc.1
  rw [if_pos ⟨hT2, hBB _ _ hT2⟩, hmu]
  obtain ⟨-, hW, -⟩ := _root_.GlobalTheory.HL.TermBasic.term_basic L r k S d' _ hT2
  simpa using (_root_.GlobalTheory.HL.WitIndep.witness_independence L r k S d' _ _ _ hW).2.2.2.2

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in

theorem _root_.GlobalTheory.HL.BadPlaces.bad_places : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : _root_.GlobalTheory.HL.Places F E sig), ∀ (r k : ℕ) (G : _root_.GlobalTheory.HL.GFrames A r k), 4 * r + 7 ≤ k → ∀ d Λ, G.IsTerm d Λ → G.Om.Finite ∧ (∀ p, 1 ≤ (G.S p).Hp) ∧ (∀ p ∈ G.Om, 2 ≤ (G.S p).q ∧ ((G.S p).q : ℝ) ≤ (G.S p).Hp) ∧ (2 : ℝ) ^ G.Om.ncard ≤ G.Ht ∧ ∀ p ∉ G.Om, (∀ d' Λ', (G.S p).IsTerm d' Λ' → (G.S p).BBzero d' Λ') ∧ ∀ d', (∃ Λ', (G.S p).IsTerm d' Λ') → ‖(G.S p).amp d' ((G.S p).BBzero d')‖ = 1 ∧ (G.S p).mass d' (fun _ => True) = 1 := by
  intro F E _ _ _ _ _ sig A r k G hk d Λ hT
  have hlf : ∀ p, IsNonarchimedeanLocalField (A.loc p).Fp := fun p => (A.loc p).lf
  have hch : ∀ p, CharZero (A.loc p).Fp := fun p => (A.loc p).char0
  have hloc : ∀ p, (G.S p).IsTerm (d p) (A.lat p Λ) := hT.2
  have hmemOm : ∀ p, p ∈ G.Om ↔ (G.S p).Hp ≠ 1 := fun p => Iff.rfl
  have h1 : ∀ p, 1 ≤ (G.S p).Hp := fun p =>
    haveI := hlf p; haveI := hch p
    (_root_.GlobalTheory.HL.Defect.exponents_and_defect _ r k (G.S p) _ _ (hloc p)).2.2.2.2.1
  have hfin : G.Om.Finite :=
    (_root_.GlobalTheory.HL.StdPlace.coordinate_lattice_standard A r k G hk).subset
      fun p hp hgood => (hmemOm p).1 hp hgood.2.1
  have hbad : ∀ p ∈ G.Om, 2 ≤ (G.S p).q ∧
      ((G.S p).q : ℝ) ≤ (G.S p).Hp := fun p hp =>
    haveI := hlf p; haveI := hch p
    ⟨two_le_q' _, q_le_Hp_of_Hp_ne_one _ (hloc p) ((hmemOm p).1 hp)⟩
  refine ⟨hfin, h1, hbad, ?_, ?_⟩
  · have hHt : G.Ht = ∏ p ∈ hfin.toFinset, (G.S p).Hp := by
      unfold _root_.GlobalTheory.HL.GFrames.Ht
      apply finprod_eq_prod_of_mulSupport_subset
      intro p hp
      simpa [hmemOm] using hp
    rw [hHt, Set.ncard_eq_toFinset_card _ hfin, ← Finset.prod_const]
    apply Finset.prod_le_prod (fun _ _ => by norm_num)
    intro p hp
    have hb := hbad p (hfin.mem_toFinset.1 hp)
    calc (2 : ℝ) ≤ (G.S p).q := by exact_mod_cast hb.1
      _ ≤ _ := hb.2
  · intro p hp
    haveI := hlf p; haveI := hch p
    have hH : (G.S p).Hp = 1 := by
      by_contra hne; exact hp ((hmemOm p).2 hne)
    obtain ⟨hgg, hG, hDl⟩ := gg_false_and_vE_eq_zero_of_Hp_eq_one _ (hloc p) hH
    refine ⟨(_root_.GlobalTheory.HL.GoodPlace.equality _ r k (G.S p) hk hgg hG hDl).1, ?_⟩
    intro d' hd'
    exact norm_amp_BBzero_eq_one_and_mass_eq_one_of_Hp_eq_one _ hk (hloc p) hH d' hd'

end GlobalTheory.HL.BadPlaces
end

section
namespace GlobalTheory.FinprodProdMulIte

open Classical in

theorem finprod_eq_prod_mul_finprod_ite {ι : Type} (S₁ : Finset ι) (f g : ι → ℂ)
    (hf : (Function.mulSupport f).Finite) (hfg : ∀ p, p ∉ S₁ → f p = g p) :
    ∏ᶠ p, f p = (∏ p ∈ S₁, f p) * ∏ᶠ p, (if p ∈ S₁ then (1 : ℂ) else g p) := by
  have hsub₁ : Function.mulSupport (fun p => if p ∈ S₁ then f p else (1 : ℂ)) ⊆ (S₁ : Set ι) := by
    intro p hp
    by_contra h
    have h' : p ∉ S₁ := h
    exact hp (by simp [h'])
  have hsub₂ : Function.mulSupport (fun p => if p ∈ S₁ then (1 : ℂ) else g p)
      ⊆ Function.mulSupport f := by
    intro p hp
    by_cases h : p ∈ S₁
    · exact absurd (by simp [h]) hp
    · intro h1
      exact hp (by simp [h, ← hfg p h, h1])
  have h₁ : ∏ᶠ p, (if p ∈ S₁ then f p else (1 : ℂ)) = ∏ p ∈ S₁, f p := by
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub₁]
    exact Finset.prod_congr rfl fun p hp => by simp [hp]
  rw [← h₁, ← finprod_mul_distrib (S₁.finite_toSet.subset hsub₁) (hf.subset hsub₂)]
  refine finprod_congr fun p => ?_
  by_cases h : p ∈ S₁
  · simp [h]
  · simp [h, hfg p h]

end GlobalTheory.FinprodProdMulIte
end

section
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.DefectPhase

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {A : Places F E sig} {r k : ℕ} (G : GFrames A r k)

theorem amp_eq_finsum (d : G.Dat) (hT : {o : Quot G.LRel | G.IsTerm d o.out}.Finite) (Q : G.Lt → Prop) :
    G.amp d Q = ∑ o ∈ hT.toFinset, if Q o.out then (G.mu o.out : ℂ) * G.om d o.out else 0 := by
  unfold GFrames.amp
  rw [tsum_eq_sum (s := hT.toFinset)]
  · refine Finset.sum_congr rfl fun o ho => ?_
    have : G.IsTerm d o.out := hT.mem_toFinset.1 ho
    simp only [this, true_and]
  · intro o ho
    have : ¬ G.IsTerm d o.out := fun h => ho (hT.mem_toFinset.2 h)
    simp only [this, false_and, if_false]

theorem finprod_split' {ι : Type} (S1 : Finset ι) (f g : ι → ℂ) (hf : (Function.mulSupport f).Finite)
    (hfg : ∀ p ∉ S1, f p = g p) :
    ∏ᶠ p, f p = (∏ p ∈ S1, f p) * ∏ᶠ p, (if p ∈ S1 then 1 else g p) := by
  first
  | exact @_root_.GlobalTheory.FinprodProdMulIte.finprod_eq_prod_mul_finprod_ite
  | exact _root_.GlobalTheory.FinprodProdMulIte.finprod_eq_prod_mul_finprod_ite
  | (apply _root_.GlobalTheory.FinprodProdMulIte.finprod_eq_prod_mul_finprod_ite <;> assumption)
  | (intros; apply _root_.GlobalTheory.FinprodProdMulIte.finprod_eq_prod_mul_finprod_ite <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FinprodProdMulIte.finprod_eq_prod_mul_finprod_ite <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FinprodProdMulIte.finprod_eq_prod_mul_finprod_ite ..)

theorem norm_finprod_eq_one {ι : Type} (g : ι → ℂ) (hg : (Function.mulSupport g).Finite)
    (h1 : ∀ p, ‖g p‖ = 1) : ‖∏ᶠ p, g p‖ = 1 := by
  rw [finprod_eq_prod_of_mulSupport_subset (s := hg.toFinset) g (fun p hp => hg.mem_toFinset.2 hp), norm_prod]
  exact Finset.prod_eq_one fun p _ => h1 p

def cond (d : G.Dat) (B : Finset (HeightOneSpectrum (𝓞 F))) (p : HeightOneSpectrum (𝓞 F)) :
    Submodule (A.L p).O (G.S p).V → Prop :=
  if p ∈ B then fun Λ => ¬ (G.S p).BBzero (d p) Λ else (G.S p).BBzero (d p)

theorem amp_cond (d : G.Dat) (B : Finset (HeightOneSpectrum (𝓞 F))) (p : HeightOneSpectrum (𝓞 F)) :
    (G.S p).amp (d p) (cond G d B p) = if p ∈ B then (G.S p).amp (d p) (fun Λ => ¬ (G.S p).BBzero (d p) Λ)
      else (G.S p).amp (d p) ((G.S p).BBzero (d p)) := by
  unfold cond
  split_ifs <;> rfl

theorem cond_pos (d : G.Dat) {B : Finset (HeightOneSpectrum (𝓞 F))} {p : HeightOneSpectrum (𝓞 F)} (h : p ∈ B)
    (Λ : Submodule (A.L p).O (G.S p).V) : cond G d B p Λ ↔ ¬ (G.S p).BBzero (d p) Λ := by
  unfold cond
  rw [if_pos h]

theorem cond_neg (d : G.Dat) {B : Finset (HeightOneSpectrum (𝓞 F))} {p : HeightOneSpectrum (𝓞 F)} (h : p ∉ B)
    (Λ : Submodule (A.L p).O (G.S p).V) : cond G d B p Λ ↔ (G.S p).BBzero (d p) Λ := by
  unfold cond
  rw [if_neg h]

end GlobalTheory.HL.DefectPhase

namespace GlobalTheory.HL.DefectPhase

theorem amp_sum_defect_sets : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → ∀ d : G.Dat, (∃ Λ₀, G.IsTerm d Λ₀) → ∀ S1 : Finset (HeightOneSpectrum (𝓞 F)), G.Om ⊆ S1 → ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ Q : Prop → Prop, G.amp d (fun Λ => Q (¬ G.Gen d Λ)) = κ * ∑ B ∈ S1.powerset.filter (fun B => Q B.Nonempty), ∏ p ∈ S1, (if p ∈ B then (G.S p).amp (d p) (fun Λ => ¬ (G.S p).BBzero (d p) Λ) else (G.S p).amp (d p) ((G.S p).BBzero (d p))) := by
  intro F E _ _ _ _ _ sig A r k G hk d hex S1 hS1
  obtain ⟨Λ₀, hΛ₀⟩ := hex
  obtain ⟨-, -, -, -, hgood⟩ := GlobalTheory.HL.BadPlaces.bad_places A r k G hk d Λ₀ hΛ₀
  have hinv : ∀ p, ∀ h ∈ (G.S p).St, ∀ Λ, (G.S p).IsTerm (d p) Λ →
      ((G.S p).BBzero (d p) (h • Λ) ↔ (G.S p).BBzero (d p) Λ) := by
    intro p h hh Λ hΛ
    have := (A.loc p).lf
    have := (A.loc p).char0
    exact (GlobalTheory.FrameAct.stabiliser_acts_on_terms _ r k (G.S p) (d p) Λ hΛ h hh).2.2.2.2.2.2.2.1
  have hBB : ∀ p ∉ (S1 : Set _), ∀ Λ, (G.S p).IsTerm (d p) Λ → (G.S p).BBzero (d p) Λ :=
    fun p hp Λ hΛ => (hgood p fun h => hp (hS1 h)).1 _ _ hΛ
  have hprod : ∀ B : Finset (HeightOneSpectrum (𝓞 F)), B ⊆ S1 →
      G.amp d (fun Λ => ∀ p, cond G d B p (A.lat p Λ)) = ∏ᶠ p, (G.S p).amp (d p) (cond G d B p) ∧
      {p | (G.S p).amp (d p) (cond G d B p) ≠ 1 ∨ (G.S p).mass (d p) (cond G d B p) ≠ 1}.Finite ∧
      {o : Quot G.LRel | G.IsTerm d o.out}.Finite := by
    intro B hB
    have hI : ∀ p, ∀ h ∈ (G.S p).St, ∀ Λ, (G.S p).IsTerm (d p) Λ → cond G d B p Λ →
        cond G d B p (h • Λ) := by
      intro p h hh Λ hΛ hP
      by_cases hp : p ∈ B
      · rw [cond_pos G d hp] at hP ⊢
        rwa [hinv p h hh Λ hΛ]
      · rw [cond_neg G d hp] at hP ⊢
        rwa [hinv p h hh Λ hΛ]
    have hF : {p | ∃ Λ, (G.S p).IsTerm (d p) Λ ∧ ¬ cond G d B p Λ}.Finite := by
      refine S1.finite_toSet.subset fun p ⟨Λ, hΛ, hP⟩ => ?_
      by_contra hp
      have hpB : p ∉ B := fun h => hp (hB h)
      rw [cond_neg G d hpB] at hP
      exact hP (hBB p hp Λ hΛ)
    obtain ⟨a1, -, a3, a4⟩ := GlobalTheory.T.hermitian_amplitude_mass_product_structure A r k G hk d ⟨Λ₀, hΛ₀⟩ (cond G d B) hI hF
    exact ⟨a1, a3, a4⟩
  have hT := (hprod ∅ (Finset.empty_subset _)).2.2
  set g : HeightOneSpectrum (𝓞 F) → ℂ := fun p => (G.S p).amp (d p) ((G.S p).BBzero (d p)) with hg
  set c : ℂ := ∏ᶠ p, (if p ∈ S1 then 1 else g p) with hc
  have hsupp : ∀ B : Finset (HeightOneSpectrum (𝓞 F)), B ⊆ S1 →
      (Function.mulSupport fun p => (G.S p).amp (d p) (cond G d B p)).Finite := fun B hB =>
    (hprod B hB).2.1.subset fun p hp => Or.inl hp
  have hsplit : ∀ B : Finset (HeightOneSpectrum (𝓞 F)), B ⊆ S1 →
      G.amp d (fun Λ => ∀ p, cond G d B p (A.lat p Λ)) =
        c * ∏ p ∈ S1, (if p ∈ B then (G.S p).amp (d p) (fun Λ => ¬ (G.S p).BBzero (d p) Λ)
          else (G.S p).amp (d p) ((G.S p).BBzero (d p))) := by
    intro B hB
    rw [(hprod B hB).1, finprod_split' S1 _ g (hsupp B hB), mul_comm]
    · rw [Finset.prod_congr rfl fun p _ => amp_cond G d B p]
    · intro p hp
      have hpB : p ∉ B := fun h => hp (hB h)
      rw [amp_cond, if_neg hpB]
  have hc1 : ‖c‖ = 1 := by
    refine norm_finprod_eq_one _ ?_ fun p => ?_
    · refine (hsupp ∅ (Finset.empty_subset _)).subset fun p hp => ?_
      by_cases h : p ∈ S1
      · exact absurd (if_pos h) hp
      · change (G.S p).amp (d p) (cond G d ∅ p) ≠ 1
        rw [amp_cond, if_neg (Finset.notMem_empty p)]
        simpa [h] using hp
    · by_cases h : p ∈ S1
      · simp [h]
      · simp only [h, if_false, hg]
        exact ((hgood p fun hp => h (hS1 hp)).2 (d p) ⟨A.lat p Λ₀, hΛ₀.2 p⟩).1
  refine ⟨c, hc1, fun Q => ?_⟩
  have hsum : G.amp d (fun Λ => Q (¬ G.Gen d Λ)) = ∑ B ∈ S1.powerset.filter (fun B => Q B.Nonempty),
      G.amp d (fun Λ => ∀ p, cond G d B p (A.lat p Λ)) := by
    rw [amp_eq_finsum G d hT]
    simp only [amp_eq_finsum G d hT]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun o ho => ?_
    have hto : ∀ p, (G.S p).IsTerm (d p) (A.lat p o.out) := (hT.mem_toFinset.1 ho).2
    have hS : ∀ p, ¬ (G.S p).BBzero (d p) (A.lat p o.out) → p ∈ S1 := fun p hn => by
      by_contra hp
      exact hn (hBB p hp _ (hto p))
    set B₀ := S1.filter fun p => ¬ (G.S p).BBzero (d p) (A.lat p o.out) with hB₀
    have hgen : (¬ G.Gen d o.out) = B₀.Nonempty := by
      apply propext
      constructor
      · intro h
        obtain ⟨p, hp⟩ := not_forall.1 h
        exact ⟨p, Finset.mem_filter.2 ⟨hS p hp, hp⟩⟩
      · rintro ⟨p, hp⟩ h
        exact (Finset.mem_filter.1 hp).2 (h p)
    have heq : ∀ B ∈ S1.powerset.filter (fun B => Q B.Nonempty),
        (if ∀ p, cond G d B p (A.lat p o.out) then (G.mu o.out : ℂ) * G.om d o.out else 0) =
          if B₀ = B then (G.mu o.out : ℂ) * G.om d o.out else 0 := by
      intro B hB
      have hBS : B ⊆ S1 := Finset.mem_powerset.1 (Finset.mem_filter.1 hB).1
      have hiff : (∀ p, cond G d B p (A.lat p o.out)) ↔ B₀ = B := by
        constructor
        · intro hQ
          ext p
          constructor
          · intro hp
            by_contra hpB
            exact (Finset.mem_filter.1 hp).2 ((cond_neg G d hpB _).1 (hQ p))
          · intro hp
            exact Finset.mem_filter.2 ⟨hBS hp, (cond_pos G d hp _).1 (hQ p)⟩
        · rintro rfl p
          by_cases hp : p ∈ B₀
          · exact (cond_pos G d hp _).2 (Finset.mem_filter.1 hp).2
          · refine (cond_neg G d hp _).2 ?_
            by_contra hn
            exact hp (Finset.mem_filter.2 ⟨hS p hn, hn⟩)
      simp only [hiff]
    rw [Finset.sum_congr rfl heq, Finset.sum_ite_eq, hgen]
    have hmem : B₀ ∈ S1.powerset.filter (fun B => Q B.Nonempty) ↔ Q B₀.Nonempty := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨fun h => h.2, fun h => ⟨Finset.filter_subset _ _, h⟩⟩
    by_cases hq : Q B₀.Nonempty
    · rw [if_pos hq, if_pos (hmem.2 hq)]
    · rw [if_neg hq, if_neg (fun h => hq (hmem.1 h))]
  rw [hsum, Finset.sum_congr rfl fun B hB => hsplit B (Finset.mem_powerset.1 (Finset.mem_filter.1 hB).1),
    ← Finset.mul_sum]

end GlobalTheory.HL.DefectPhase
end

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitude_expansion_over_finite_places : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → ∀ d : G.Dat, (∃ Λ₀, G.IsTerm d Λ₀) → ∀ S1 : Finset (HeightOneSpectrum (𝓞 F)), G.Om ⊆ S1 → ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ Q : Prop → Prop, G.amp d (fun Λ => Q (¬ G.Gen d Λ)) = κ * ∑ B ∈ S1.powerset.filter (fun B => Q B.Nonempty), ∏ p ∈ S1, (if p ∈ B then (G.S p).amp (d p) (fun Λ => ¬ (G.S p).BBzero (d p) Λ) else (G.S p).amp (d p) ((G.S p).BBzero (d p))) := by
  atlas_forward_decl GlobalTheory.HL.DefectPhase.amp_sum_defect_sets
end

section
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.TermOrbit

section Gen

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {m : ℕ}

def Fl (R : Type) [CommRing R] [Module R V] (f : Fin m → V) (b : Fin m) : Submodule R V :=
  Submodule.span R (f '' {i | (i : ℕ) < (b : ℕ)})

def UT (R : Type) [CommRing R] [Module R V] (φ : V → V) (f g : Fin m → V) : Prop :=
  ∀ b, φ (f b) - g b ∈ Fl R g b

theorem mem_Fl {f : Fin m → V} {a b : Fin m} (h : a < b) : f a ∈ Fl R f b :=
  Submodule.subset_span ⟨a, Fin.lt_def.1 h, rfl⟩

theorem Fl_mono {f : Fin m → V} {a b : Fin m} (h : a ≤ b) : Fl R f a ≤ Fl R f b :=
  Submodule.span_mono (Set.image_mono fun i (hi : (i : ℕ) < a) => lt_of_lt_of_le hi (Fin.le_def.1 h))

theorem map_Fl (φ : V →ₗ[R] V) {f g : Fin m → V} (h : UT R φ f g) (b : Fin m) :
    ∀ x ∈ Fl R f b, φ x ∈ Fl R g b := by
  intro x hx
  have hle : Fl R f b ≤ (Fl R g b).comap φ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    have hab : a < b := Fin.lt_def.2 ha
    show φ (f a) ∈ Fl R g b
    have e : φ (f a) = (φ (f a) - g a) + g a := by abel
    rw [e]
    exact Submodule.add_mem _ (Fl_mono hab.le (h a)) (mem_Fl hab)
  exact hle hx

theorem UT.comp (φ₂ : V ≃ₗ[R] V) {φ₁ : V → V} {f g k : Fin m → V} (h₁ : UT R φ₁ f g) (h₂ : UT R φ₂ g k) :
    UT R (fun x => φ₂ (φ₁ x)) f k := by
  intro b
  have e : φ₂ (φ₁ (f b)) - k b = φ₂ (φ₁ (f b) - g b) + (φ₂ (g b) - k b) := by
    rw [map_sub]; abel
  rw [e]
  exact Submodule.add_mem _ (map_Fl (φ₂ : V →ₗ[R] V) h₂ b _ (h₁ b)) (h₂ b)

theorem UT.trans_id {φ : V → V} {f g k : Fin m → V} (h₁ : UT R φ f g) (h₂ : UT R id g k) : UT R φ f k :=
  UT.comp (LinearEquiv.refl R V) h₁ h₂

def conjH {W : Type} [AddCommGroup W] [Module R W] (e : V ≃ₗ[R] W) : (V ≃ₗ[R] V) →* (W ≃ₗ[R] W) where
  toFun g := e.symm.trans (g.trans e)
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

theorem conjH_apply {W : Type} [AddCommGroup W] [Module R W] (e : V ≃ₗ[R] W) (g : V ≃ₗ[R] V) (v : V) :
    conjH e g (e v) = e (g v) := by
  simp [conjH]

theorem UT.of_eq {φ : V → V} {f g : Fin m → V} (h : ∀ b, φ (f b) = g b) : UT R φ f g := by
  intro b; rw [h b, sub_self]; exact Submodule.zero_mem _

theorem UT.of_matrix (A : Matrix (Fin m) (Fin m) R) (h0 : ∀ a b, b < a → A a b = 0) (h1 : ∀ a, A a a = 1)
    {φ : V → V} {f g : Fin m → V} (h : ∀ b, φ (f b) = ∑ a, A a b • g a) : UT R φ f g := by
  intro b
  rw [h b, ← Finset.add_sum_erase _ _ (Finset.mem_univ b), h1 b, one_smul, add_sub_cancel_left]
  refine Submodule.sum_mem _ fun a ha => ?_
  rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase ha) with hab | hab
  · exact Submodule.smul_mem _ _ (mem_Fl hab)
  · rw [h0 a b hab, zero_smul]; exact Submodule.zero_mem _

theorem mem_Fl_map {W : Type} [AddCommGroup W] [Module R W] (e : V ≃ₗ[R] W) {f : Fin m → V} {b : Fin m}
    {x : V} (hx : x ∈ Fl R f b) : e x ∈ Fl R (fun a => e (f a)) b := by
  have h := Submodule.mem_map_of_mem (f := (e : V →ₗ[R] W)) hx
  rw [Fl, Submodule.map_span, ← Set.image_comp] at h
  exact h

end Gen

end GlobalTheory.HL.TermOrbit

namespace GlobalTheory.HL.TermOrbit

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : Frames L r k)

theorem ut_of_Nof (g : Fin (r + 1) → S.V) (t : E)
    (hg : ∀ a b, hf L S.Hm (g a) (g b) = if a = Fin.last r ∧ b = Fin.last r then t else 0)
    {n : S.GLV} (hn : n ∈ S.Nof g) : UT E n g g := by
  simp only [Frames.Nof, Subgroup.mem_inf, Subgroup.mem_iInf] at hn
  obtain ⟨⟨-, h1⟩, h2⟩ := hn
  intro b
  by_cases hb : (b : ℕ) < r
  · have e : b = (⟨b, hb⟩ : Fin r).castSucc := Fin.ext rfl
    have := (h1 ⟨b, hb⟩).2 (g b) (Submodule.subset_span ⟨b, by simp, rfl⟩)
    exact this
  · have hr : b = Fin.last r := Fin.ext (by have := b.2; simp only [Fin.val_last]; omega)
    subst hr
    refine h2.2 _ ?_
    refine GlobalTheory.FramePsi.hf_span_right L S.Hm _ _ ?_
    rintro _ ⟨l, hl, rfl⟩
    rw [hg, if_neg]
    rintro ⟨-, rfl⟩
    simp at hl

theorem ut_N {n : S.GLV} (hn : n ∈ S.N) : UT E n S.f S.f := ut_of_Nof S S.f _ S.gram hn

theorem ut_N' {n : S.GLV} (hn : n ∈ S.N') : UT E n S.f' S.f' := ut_of_Nof S S.f' _ S.gram' hn

end Loc

section Rat

open Formalism.L2.SG.Pf

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem ut_nlam {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V}
    (hn : n ∈ NLam Λ F) : UT E n (frame F) (frame F) := by
  intro b
  by_cases hb : (b : ℕ) < r
  · have e : b = (⟨b, hb⟩ : Fin r).castSucc := Fin.ext rfl
    rw [e, frame_castSucc_td]
    have h1 := hn.2.1 b (F.fl.e ⟨b, hb⟩) (Submodule.subset_span ⟨⟨b, hb⟩, by simp, rfl⟩)
    refine Submodule.span_le.2 ?_ h1
    rintro _ ⟨a, ha, rfl⟩
    refine Submodule.subset_span ⟨a.castSucc, ?_, frame_castSucc_td F a⟩
    simp only [Set.mem_setOf_eq, Fin.coe_castSucc] at ha ⊢
    exact ha
  · have hr : b = Fin.last r := Fin.ext (by have := b.2; simp only [Fin.val_last]; omega)
    subst hr
    rw [frame_last_td]
    have h1 := hn.2.2 F.fl.z (Formalism.MainNotions.S.Lem.Comparison₂.z_mem_orth F)
    refine Submodule.span_le.2 ?_ h1
    rintro _ ⟨a, rfl⟩
    refine Submodule.subset_span ⟨a.castSucc, ?_, frame_castSucc_td F a⟩
    simp

theorem ut_frameAct {n : ℕ} (f : Fin n → S.V) (ξ : Matrix (Fin n) (Fin n) (𝓞 E))
    (h0 : ∀ a b, b < a → ξ a b = 0) (h1 : ∀ a, ξ a a = 1) : UT E id (frameAct f ξ) f :=
  UT.of_matrix (ξ.map fun x : 𝓞 E => (x : E)) (fun a b h => by simp [h0 a b h]) (fun a => by simp [h1 a])
    (fun b => rfl)

end Rat

end GlobalTheory.HL.TermOrbit

namespace GlobalTheory.HL.TermOrbit

section Glob

open Formalism.L2.SG.Pf

variable {D : D7}

theorem ut_loc (Z : LocDat D) (p : PlF D) {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p} (hext : Ext p γ g) {f f' : Fin (D.R.rS + 1) → (VS D).V}
    (h : UT D.host.E γ f f') :
    UT (D.s.atP p).Ep g (fun a => frFac Z.δ p a • baseChange₂ D p (f a)) (fun a => frFac Z.δ p a • baseChange₂ D p (f' a)) := by
  intro b
  have e1 : g (frFac Z.δ p b • baseChange₂ D p (f b)) - frFac Z.δ p b • baseChange₂ D p (f' b) =
      frFac Z.δ p b • baseChange₂ D p (γ (f b) - f' b) := by
    rw [map_smul, hext, map_sub, smul_sub]
  rw [e1]
  refine Submodule.smul_mem _ _ ?_
  have h2 := GlobalTheory.LocExt.baseChange_mem_span p (h b)
  refine Submodule.span_le.2 ?_ h2
  rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  obtain ⟨u, hu⟩ := Formalism.L2.SG.Pf.BBTie.bt_frFac_unit Z p a
  have e2 : baseChange₂ D p (f' a) = ((u⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) • (frFac Z.δ p a • baseChange₂ D p (f' a)) := by
    rw [← hu, smul_smul, Units.inv_mul, one_smul]
  rw [e2]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)

theorem dcrel_of_eqv (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T)
    {P : LFlag (VS D) D.R.rS T' → Prop} {x y : Formalism.L2.SG.TermDef.Carrier P}
    (h : Relation.EqvGen (Formalism.L2.SG.TermDef.Rel Λ F P) x y) : Formalism.L2.SG.TermDef.DCRel Λ F x.1 y.1 := by
  induction h with
  | rel _ _ h => exact h
  | refl => exact Formalism.L2.SG.TermDef.dcrel_refl Λ F _
  | symm _ _ _ ih => exact dcrel_symm Λ F ih
  | trans _ _ _ _ _ ih1 ih2 => exact dcrel_trans Λ F ih1 ih2

theorem ut_moves {T : D.host.E} (F F0 : LFlag (VS D) D.R.rS T) (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (hU : IsUpUni U)
    (h : ∀ b, ρ (frame F b) = ∑ a, U a b • frame F0 a) : UT D.host.E ρ (frame F) (frame F0) :=
  UT.of_matrix U (fun a b hab => (hU a b).1 hab) (fun a => (hU a a).2 rfl) h

end Glob

end GlobalTheory.HL.TermOrbit

namespace GlobalTheory.HL.TermOrbit

section LocC

open Formalism.MainNotions.S.Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
  {P : LocNG.FPair H r} {S : Frames M.L r k}

theorem conj_mem_N (c : WCoord P S) {g : V ≃ₗ[E] V} (hg : g ∈ P.A.N) : conjH c.e g ∈ S.N := by
  have hle : P.A.N ≤ S.N.comap (conjH c.e) := by
    unfold LocNG.FrameD.N
    rw [Subgroup.closure_le]
    intro g hg
    exact (GlobalTheory.HL.CoordUnip.mem_NSet S c.e P.A S.f c.h_eq c.f_eq g (conjH c.e g)
      (fun v => conjH_apply _ _ _)).1 hg
  exact hle hg

theorem conj_mem_N' (c : WCoord P S) {g : V ≃ₗ[E] V} (hg : g ∈ P.B.N) : conjH c.e g ∈ S.N' := by
  have hle : P.B.N ≤ S.N'.comap (conjH c.e) := by
    unfold LocNG.FrameD.N
    rw [Subgroup.closure_le]
    intro g hg
    exact (GlobalTheory.HL.CoordUnip.mem_NSet S c.e P.B S.f' c.h_eq c.f'_eq g (conjH c.e g)
      (fun v => conjH_apply _ _ _)).1 hg
  exact hle hg

end LocC

section LocD

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : Frames L r k)

theorem datOf_St {s : S.GLV} (hs : s ∈ S.St) (Λ : Submodule L.O S.V) : S.datOf (s • Λ) = S.datOf Λ := by
  have DO := GlobalTheory.T.hermitian_lattice_datum_equivariant_flag_isometries L r k S
  have hs' := Subgroup.mem_inf.1 hs
  exact Prod.ext (DO.2.2.1 s hs'.1 Λ) (Prod.ext (DO.2.2.2.1 s hs'.2 Λ) (GlobalTheory.FrameAct.graph_smul S s hs Λ))

end LocD

end GlobalTheory.HL.TermOrbit

namespace GlobalTheory.HL.TermOrbit

section LocO

open Formalism.MainNotions.S.Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
  {P : LocNG.FPair H r} {S : Frames M.L r k}

theorem local_orbit (hM : M.OK) (c : WCoord P S) {d d' : LocNG.Datum P} (hdd : LocNG.Datum.Rel d d')
    {t : Term V M r} (ht : LocNG.IsTermOver P d' t) (ψ0 : V ≃ₗ[E] V) (hu : LocNG.IsUnitary H ψ0)
    (hA : UT E ψ0 t.f P.A.f) (hB : UT E ψ0 t.f' P.B.f) (X : Submodule M.L.O S.V)
    (hX : conjH c.e ψ0 • c.lat t.abelian₂ = X) : ∃ h ∈ S.H0, h • c.dat d = S.datOf X := by
  haveI := hM.loc
  haveI := hM.char0
  have ht' := ht
  obtain ⟨-, -, ⟨nA, hnA, hfA, -⟩, ⟨nB, hnB, hfB, -⟩, -⟩ := ht'
  have hφ : ∀ v, conjH c.e ψ0 (c.e v) = c.e (ψ0 v) := conjH_apply _ _
  have hνA := conj_mem_N c hnA
  have hνB := conj_mem_N' c hnB
  have k1 : UT E ((conjH c.e nA).trans (conjH c.e ψ0)) S.f S.f := by
    intro b
    have hb : nA (P.A.f b) = t.f b := (congrFun hfA b).symm
    rw [LinearEquiv.trans_apply, c.f_eq b, conjH_apply, hφ, hb, ← map_sub,
      show S.f = fun a => c.e (P.A.f a) from funext c.f_eq]
    exact mem_Fl_map c.e (hA b)
  have k1' : UT E ((conjH c.e nB).trans (conjH c.e ψ0)) S.f' S.f' := by
    intro b
    have hb : nB (P.B.f b) = t.f' b := (congrFun hfB b).symm
    rw [LinearEquiv.trans_apply, c.f'_eq b, conjH_apply, hφ, hb, ← map_sub,
      show S.f' = fun a => c.e (P.B.f a) from funext c.f'_eq]
    exact mem_Fl_map c.e (hB b)
  have k2 : UT E (conjH c.e nA).symm S.f S.f := ut_N S (S.N.inv_mem hνA)
  have k2' : UT E (conjH c.e nB).symm S.f' S.f' := ut_N' S (S.N'.inv_mem hνB)
  have hf1 : ∀ b : Fin (r + 1), conjH c.e ψ0 (S.f b) - S.f b ∈ S.spanTo S.f b := by
    intro b
    have h := UT.comp _ k2 k1 b
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply] at h
    exact h
  have hf2 : ∀ b : Fin (r + 1), conjH c.e ψ0 (S.f' b) - S.f' b ∈ S.spanTo S.f' b := by
    intro b
    have h := UT.comp _ k2' k1' b
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply] at h
    exact h
  have hiso : conjH c.e ψ0 ∈ isomG M.L S.Hm := by
    intro x y
    obtain ⟨x, rfl⟩ := c.e.surjective x
    obtain ⟨y, rfl⟩ := c.e.surjective y
    show S.h (conjH c.e ψ0 (c.e x)) (conjH c.e ψ0 (c.e y)) = S.h (c.e x) (c.e y)
    rw [hφ, hφ, c.h_eq, c.h_eq, hu]
  have DO := GlobalTheory.T.hermitian_lattice_datum_equivariant_flag_isometries M.L r k S
  obtain ⟨s, hs, h, hh, hsh⟩ := DO.2.2.2.2 _ hiso hf1 hf2
  have W := GlobalTheory.T.terms_orbits_heights_amplitudes_in_coordinates M hM H r k P S c
  obtain ⟨h1, hh1, hd⟩ := (W.2.1 d d').1 hdd
  have hterm := (W.1 d' t ht).1
  have hM' := DO.1 _ _ hterm
  refine ⟨h * h1, S.H0.mul_mem hh hh1, ?_⟩
  rw [← hX, hsh, mul_smul s h, datOf_St S hs, DO.2.1 h hh, ← hM', ← hd, mul_smul h h1]

end LocO

end GlobalTheory.HL.TermOrbit

namespace GlobalTheory.HL.TermOrbit

section GlobL

variable {D : D7}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000 in

theorem lat_move_loc (Z : LocDat D) (p : PlF D) {FP : LocNG.FPair (locH Z p) D.R.rS} {k : ℕ}
    {S : Frames (Z.M p).L D.R.rS k} (cp : WCoord FP S) (ρ n : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hn : ∀ x, n x ∈ Λ ↔ x ∈ Λ)
    (gl ρp : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (hext : Ext p (ρ * n⁻¹) ρp) :
    conjH cp.e (gl.symm.trans ρp) • cp.lat (LocNG.img (M := Z.M p) gl (lattice₂ D Z.M p Λ)) =
      Submodule.span (Z.M p).L.O ((fun y => cp.e (baseChange₂ D p (ρ y))) '' (Λ : Set (VS D).V)) := by
  have hset : ∀ y, conjH cp.e (gl.symm.trans ρp) (cp.e (gl (baseChange₂ D p y))) = cp.e (baseChange₂ D p (ρ (n⁻¹ y))) := by
    intro y
    rw [conjH_apply, LinearEquiv.trans_apply, gl.symm_apply_apply, hext]
    rfl
  have hL : cp.lat (LocNG.img (M := Z.M p) gl (lattice₂ D Z.M p Λ)) =
      Submodule.span _ ((fun y => cp.e (gl (baseChange₂ D p y))) '' (Λ : Set (VS D).V)) := by
    simp only [WCoord.lat, LocNG.img, lattice₂, Submodule.map_span, Set.image_image]
    rfl
  rw [hL, Submodule.pointwise_smul_def, Submodule.map_span, Set.image_image]
  have hfun : (fun x => (DistribSMul.toLinearMap (Z.M p).L.O S.V (conjH cp.e (gl.symm.trans ρp)))
      (cp.e (gl (baseChange₂ D p x)))) = fun x => cp.e (baseChange₂ D p (ρ (n⁻¹ x))) := funext fun x => hset x
  rw [hfun]
  congr 1
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : n⁻¹ x ∈ Λ := (hn (n⁻¹ x)).1 (by rwa [show n (n⁻¹ x) = x from n.apply_symm_apply x])
    exact ⟨n⁻¹ x, hx', rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨n y, (hn y).2 hy, ?_⟩
    show cp.e (baseChange₂ D p (ρ (n.symm (n y)))) = _
    rw [n.symm_apply_apply]

end GlobL

end GlobalTheory.HL.TermOrbit

namespace GlobalTheory.HL.TermOrbit

open Formalism.L2.SG.Pf

set_option maxHeartbeats 1000000 in

theorem datum_in_orbit : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (p : PlF D) (d : LocNG.Datum (FP p)), Over (FP p) d (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t₀.toTerm.lam (lf D (X.Fu u)) (Quot.out t₀.toTerm.cls).1 (Tu D u) (Tu D u')) → ∀ δ : G.Dat, δ p = (c.c p).dat d → ∃ h ∈ (G.S p).H0, h • δ p = G.datOf (c.lat ρ t₀.lam) p := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hAB G c t₀ ρ U U' hMv p d hOv δ hδ
  obtain ⟨gl, hgl, d', hdd', hTO⟩ := hOv
  have hOK : (Y.M p).OK := (Y.agree p).1
  haveI := hOK.loc
  haveI := hOK.char0
  have hTOc := hTO
  obtain ⟨-, -, ⟨nA, hnA, hfA, -⟩, ⟨nB, hnB, hfB, -⟩, -⟩ := hTO

  have hq : Relation.EqvGen (Formalism.L2.SG.TermDef.Rel t₀.lam (lf D (X.Fu u)) (Formalism.L2.SG.TermDef.PD D t₀.lam (lf D (X.Fu u)) u'))
      (Quot.out t₀.toTerm.cls) ⟨t₀.frame, t₀.rep.2.2.2.2⟩ := Quot.eqvGen_exact (Quot.out_eq _)
  obtain ⟨n, hn, m, hm, hfr, -⟩ := dcrel_symm _ _ (dcrel_of_eqv _ _ hq)

  have RA : UT D.host.E (ρ * n⁻¹) (frame (lf D (X.Fu u))) (frame F00) :=
    UT.comp ρ (ut_nlam (nlamPf_inv hn)) (ut_moves _ _ ρ U hMv.2.1 hMv.2.2.2.1)
  have hxi := admissibility_witness_unitriangular t₀.lam (lf D (X.Fu u)) (Quot.out t₀.toTerm.cls).1
  have hxi' := inv_unitri _ hxi.1 hxi.2
  have RB : UT D.host.E (ρ * n⁻¹)
      (frameAct (frame (Quot.out t₀.toTerm.cls).1) (admXi D t₀.lam (lf D (X.Fu u)) (Quot.out t₀.toTerm.cls).1)⁻¹)
      (frame F'0) := by
    have s1 := ut_frameAct (frame (Quot.out t₀.toTerm.cls).1) _ hxi'.1 hxi'.2
    have s2 : UT D.host.E ⇑(n⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (frame (Quot.out t₀.toTerm.cls).1) (fun a => m (frame t₀.frame a)) :=
      UT.of_eq fun b => by
        rw [show frame (Quot.out t₀.toTerm.cls).1 b = n (m (frame t₀.frame b)) from hfr b]; simp
    have s3 : UT D.host.E id (fun a => m (frame t₀.frame a)) (frame t₀.frame) := fun b => ut_nlam hm b
    have s4 := ut_moves _ _ ρ U' hMv.2.2.1 hMv.2.2.2.2
    exact UT.comp ρ (UT.trans_id (UT.comp n⁻¹ s1 s2) s3) s4
  have hγ : ρ * n⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := Subgroup.mul_mem _ hMv.1 (nlamPf_inv hn).1.1
  obtain ⟨ρp, hρe, hρu, -, -, -⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D ⟨Y.δ, Y.M, Y.agree⟩ p (ρ * n⁻¹) hγ

  have UA : UT (D.s.atP p).Ep ρp
      (locU ⟨Y.δ, Y.M, Y.agree⟩ p t₀.toTerm.lam (lf D (X.Fu u)) (Quot.out t₀.toTerm.cls).1 (Tu D u) (Tu D u')).f
      (FP p).A.f := by
    rw [(hAB p).1.1]
    exact ut_loc ⟨Y.δ, Y.M, Y.agree⟩ p hρe RA
  have UB : UT (D.s.atP p).Ep ρp
      (locU ⟨Y.δ, Y.M, Y.agree⟩ p t₀.toTerm.lam (lf D (X.Fu u)) (Quot.out t₀.toTerm.cls).1 (Tu D u) (Tu D u')).f'
      (FP p).B.f := by
    rw [(hAB p).1.2.1]
    exact ut_loc ⟨Y.δ, Y.M, Y.agree⟩ p hρe RB
  have hA : UT (D.s.atP p).Ep (gl.symm.trans ρp)
      (move gl (locU ⟨Y.δ, Y.M, Y.agree⟩ p t₀.toTerm.lam (lf D (X.Fu u)) (Quot.out t₀.toTerm.cls).1 (Tu D u)
        (Tu D u'))).f (FP p).A.f := fun b => by
    show ρp (gl.symm (gl _)) - _ ∈ _
    rw [gl.symm_apply_apply]
    exact UA b
  have hB : UT (D.s.atP p).Ep (gl.symm.trans ρp)
      (move gl (locU ⟨Y.δ, Y.M, Y.agree⟩ p t₀.toTerm.lam (lf D (X.Fu u)) (Quot.out t₀.toTerm.cls).1 (Tu D u)
        (Tu D u'))).f' (FP p).B.f := fun b => by
    show ρp (gl.symm (gl _)) - _ ∈ _
    rw [gl.symm_apply_apply]
    exact UB b
  have hu : LocNG.IsUnitary (locH ⟨Y.δ, Y.M, Y.agree⟩ p) (gl.symm.trans ρp) := fun x y => by
    show (locH ⟨Y.δ, Y.M, Y.agree⟩ p).h (ρp (gl.symm x)) (ρp (gl.symm y)) = _
    rw [hρu, ← hgl (gl.symm x) (gl.symm y), gl.apply_symm_apply, gl.apply_symm_apply]

  have hn' : ∀ x, n x ∈ t₀.lam ↔ x ∈ t₀.lam := ((isAutLam_iff _ n).1 hn.1).2
  have hX1 := lat_move_loc ⟨Y.δ, Y.M, Y.agree⟩ p (c.c p) ρ n t₀.toTerm.lam hn' gl ρp hρe
  have hs : ((fun y => (c.c p).e (baseChange₂ D p (ρ y))) '' (t₀.lam : Set (VS D).V)) =
      (placesOf ⟨Y.δ, Y.M, Y.agree⟩).bc p '' ((c.lat ρ t₀.lam : Submodule (𝓞 D.host.E) G.V) : Set G.V) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨c.e (ρ y), ⟨y, hy, rfl⟩, (c.compat p (ρ y)).symm⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, c.compat p (ρ y)⟩
  have hX2 : Submodule.span (Y.M p).L.O ((fun y => (c.c p).e (baseChange₂ D p (ρ y))) '' (t₀.lam : Set (VS D).V)) =
      (placesOf ⟨Y.δ, Y.M, Y.agree⟩).lat p (c.lat ρ t₀.lam) := by
    rw [hs]
    rfl
  rw [hδ]
  exact local_orbit hOK (c.c p) hdd' hTOc (gl.symm.trans ρp) hu hA hB _ (hX1.trans hX2)

end GlobalTheory.HL.TermOrbit
end
end

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localDatum_of_term_in_movedLattice_orbit : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (p : PlF D) (d : LocNG.Datum (FP p)), Over (FP p) d (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t₀.toTerm.lam (lf D (X.Fu u)) (Quot.out t₀.toTerm.cls).1 (Tu D u) (Tu D u')) → ∀ δ : G.Dat, δ p = (c.c p).dat d → ∃ h ∈ (G.S p).H0, h • δ p = G.datOf (c.lat ρ t₀.lam) p := by
  atlas_forward_decl GlobalTheory.HL.TermOrbit.datum_in_orbit
end

section
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.AmpLoc

set_option maxHeartbeats 1000000 in

theorem global_amp_local : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (R : ∀ p, LocNG.Reps (FP p)) (S1 : Finset (PlF D)) (Om : Finset {p // p ∈ S1}) (d : ∀ p : {p // p ∈ S1}, LocNG.Datum (FP p.1)), (∀ p, p ∉ S1 → (FP p).PrimeTo) → (∀ p, p ∈ Om ↔ ¬ (FP p.1).PrimeTo) → (∀ p : {p // p ∈ S1}, Over (FP p.1) (d p) (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1 t₀.toTerm.lam (lf D (X.Fu u)) (Quot.out t₀.toTerm.cls).1 (Tu D u) (Tu D u'))) → ∀ Q : Prop → Prop, ‖G.amp (G.datOf (c.lat ρ t₀.lam)) (fun Γ => Q (¬ G.Gen (G.datOf (c.lat ρ t₀.lam)) Γ))‖ = ‖∑ A ∈ Om.powerset.filter (fun A => Q A.Nonempty), ∏ p, (if p ∈ A then LocNG.amp (R p.1) (d p) (LocNG.BBne (H := locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1)) else LocNG.amp (R p.1) (d p) (fun t => ¬ LocNG.BBne (H := locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1) t))‖ := by
  intro D X Y u u' hst hk w F00 F'0 FP hw hG hbase G c t₀ ρ U U' hmv R S1 Om d hout hOm hover Q
  have hT : G.IsTerm (G.datOf (c.lat ρ t₀.lam)) (c.lat ρ t₀.lam) :=
    (GlobalTheory.T.movedTermLattice_isGlobalTerm_phase D X Y u u' hst hk w F00 F'0 FP hw hG hbase G c t₀ ρ U U' hmv).1
  have hW := fun p => GlobalTheory.T.terms_orbits_heights_amplitudes_in_coordinates (Y.M p) (Y.agree p).1 (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p)
    D.R.rS D.R.k (FP p) (G.S p) (c.c p)
  obtain ⟨-, -, -, -, hgood⟩ := GlobalTheory.HL.BadPlaces.bad_places _ _ _ G hk _ _ hT
  have hOmS : G.Om ⊆ (S1 : Set (PlF D)) := by
    intro p hp
    by_contra hn
    exact hp ((hW p).2.2.2.1 (hout p hn))
  obtain ⟨κ, hκ, hdec⟩ := GlobalTheory.T.amplitude_expansion_over_finite_places _ _ _ G hk _ ⟨_, hT⟩ S1 hOmS
  rw [hdec Q, norm_mul, hκ, one_mul]

  have hloc : ∀ p : {p // p ∈ S1},
      (G.S p.1).amp (G.datOf (c.lat ρ t₀.lam) p.1)
          (fun Λ => ¬ (G.S p.1).BBzero (G.datOf (c.lat ρ t₀.lam) p.1) Λ) =
        LocNG.amp (R p.1) (d p) (LocNG.BBne (H := locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1)) ∧
      (G.S p.1).amp (G.datOf (c.lat ρ t₀.lam) p.1) ((G.S p.1).BBzero (G.datOf (c.lat ρ t₀.lam) p.1)) =
        LocNG.amp (R p.1) (d p) (fun t => ¬ LocNG.BBne (H := locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1) t) := by
    intro p
    haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p.1).lf
    haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p.1).char0
    have hu : (Function.update (G.datOf (c.lat ρ t₀.lam)) p.1 ((c.c p.1).dat (d p))) p.1 = (c.c p.1).dat (d p) :=
      Function.update_self _ _ _
    obtain ⟨h, hh, hδ⟩ := GlobalTheory.T.localDatum_of_term_in_movedLattice_orbit D X Y u u' hst hk w F00 F'0 FP hw hG hbase G c t₀ ρ U U' hmv p.1 (d p)
      (hover p) _ hu
    rw [hu] at hδ
    obtain ⟨e1, e2⟩ := (hW p.1).2.2.2.2 (R p.1) (d p)
    rw [e1, e2, ← hδ]
    constructor
    · refine (GlobalTheory.InvH.amp_mass_smul _ _ _ _ h hh _ _ _ ?_ ?_).1
      · intro s hs Λ hΛ hq hb
        exact hq ((GlobalTheory.FrameAct.stabiliser_acts_on_terms _ _ _ _ _ Λ hΛ s hs).2.2.2.2.2.2.2.1.1 hb)
      · intro Λ hΛ
        obtain ⟨-, -, -, hM, hs, -⟩ := GlobalTheory.HL.ComplAct.main _ _ _ _ _ Λ hΛ h hh
        exact not_congr ⟨fun e => hM.trans (e.trans hs.symm), fun e => hM.symm.trans (e.trans hs)⟩
    · refine (GlobalTheory.InvH.amp_mass_smul _ _ _ _ h hh _ _ _ ?_ ?_).1
      · intro s hs Λ hΛ hq
        exact (GlobalTheory.FrameAct.stabiliser_acts_on_terms _ _ _ _ _ Λ hΛ s hs).2.2.2.2.2.2.2.1.2 hq
      · intro Λ hΛ
        obtain ⟨-, -, -, hM, hs, -⟩ := GlobalTheory.HL.ComplAct.main _ _ _ _ _ Λ hΛ h hh
        exact ⟨fun e => hM.trans (e.trans hs.symm), fun e => hM.symm.trans (e.trans hs)⟩
  have hzero : ∀ p ∈ S1, (FP p).PrimeTo →
      (G.S p).amp (G.datOf (c.lat ρ t₀.lam) p) (fun Λ => ¬ (G.S p).BBzero (G.datOf (c.lat ρ t₀.lam) p) Λ) = 0 := by
    intro p _ hp
    have hBB := (hgood p (fun hm => hm ((hW p).2.2.2.1 hp))).1
    unfold Frames.amp
    exact (tsum_congr fun o => if_neg fun hh => hh.2 (hBB _ _ hh.1)).trans tsum_zero
  congr 1
  symm
  let emb : {p // p ∈ S1} ↪ PlF D := Function.Embedding.subtype _
  let embF : Finset {p // p ∈ S1} ↪ Finset (PlF D) := ⟨fun A => A.map emb, Finset.map_injective emb⟩
  calc _ = ∑ A ∈ Om.powerset.filter (fun A => Q A.Nonempty), ∏ p ∈ S1,
          (if p ∈ A.map emb then (G.S p).amp (G.datOf (c.lat ρ t₀.lam) p)
              (fun Λ => ¬ (G.S p).BBzero (G.datOf (c.lat ρ t₀.lam) p) Λ)
            else (G.S p).amp (G.datOf (c.lat ρ t₀.lam) p) ((G.S p).BBzero (G.datOf (c.lat ρ t₀.lam) p))) := by
        refine Finset.sum_congr rfl fun A _ => ?_
        rw [← Finset.prod_coe_sort S1]
        refine Finset.prod_congr rfl fun p _ => ?_
        have hm : (p.1 ∈ A.map emb) ↔ p ∈ A := Finset.mem_map' emb
        by_cases hp : p ∈ A
        · rw [if_pos hp, if_pos (hm.2 hp), (hloc p).1]
        · rw [if_neg hp, if_neg (fun h => hp (hm.1 h)), (hloc p).2]
    _ = ∑ B ∈ (Om.powerset.filter (fun A => Q A.Nonempty)).map embF, ∏ p ∈ S1,
          (if p ∈ B then (G.S p).amp (G.datOf (c.lat ρ t₀.lam) p)
              (fun Λ => ¬ (G.S p).BBzero (G.datOf (c.lat ρ t₀.lam) p) Λ)
            else (G.S p).amp (G.datOf (c.lat ρ t₀.lam) p) ((G.S p).BBzero (G.datOf (c.lat ρ t₀.lam) p))) :=
        by rw [Finset.sum_map]; rfl
    _ = _ := by
        apply Finset.sum_subset
        · intro B hB
          obtain ⟨A, hA, rfl⟩ := Finset.mem_map.1 hB
          rw [Finset.mem_filter, Finset.mem_powerset] at hA ⊢
          refine ⟨fun x hx => ?_, ?_⟩
          · obtain ⟨y, -, rfl⟩ := Finset.mem_map.1 hx
            exact y.2
          · show Q (A.map emb).Nonempty
            rw [Finset.map_nonempty]
            exact hA.2
        · intro B hB hn
          rw [Finset.mem_filter, Finset.mem_powerset] at hB
          by_cases hall : ∀ p ∈ B, ¬ (FP p).PrimeTo
          · exfalso
            apply hn
            have e : (B.subtype (· ∈ S1)).map emb = B := Finset.subtype_map_of_mem hB.1
            refine Finset.mem_map.2 ⟨B.subtype (· ∈ S1), ?_, e⟩
            rw [Finset.mem_filter, Finset.mem_powerset]
            refine ⟨fun q hq => (hOm q).2 (hall q.1 (Finset.mem_subtype.1 hq)), ?_⟩
            rw [← Finset.map_nonempty (f := emb), e]
            exact hB.2
          · push_neg at hall
            obtain ⟨p, hpB, hp⟩ := hall
            exact Finset.prod_eq_zero (hB.1 hpB) (by rw [if_pos hpB]; exact hzero p (hB.1 hpB) hp)

end GlobalTheory.HL.AmpLoc
end

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalAmplitude_eq_localAmplitudes : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (R : ∀ p, LocNG.Reps (FP p)) (S1 : Finset (PlF D)) (Om : Finset {p // p ∈ S1}) (d : ∀ p : {p // p ∈ S1}, LocNG.Datum (FP p.1)), (∀ p, p ∉ S1 → (FP p).PrimeTo) → (∀ p, p ∈ Om ↔ ¬ (FP p.1).PrimeTo) → (∀ p : {p // p ∈ S1}, Over (FP p.1) (d p) (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1 t₀.toTerm.lam (lf D (X.Fu u)) (Quot.out t₀.toTerm.cls).1 (Tu D u) (Tu D u'))) → ∀ Q : Prop → Prop, ‖G.amp (G.datOf (c.lat ρ t₀.lam)) (fun Γ => Q (¬ G.Gen (G.datOf (c.lat ρ t₀.lam)) Γ))‖ = ‖∑ A ∈ Om.powerset.filter (fun A => Q A.Nonempty), ∏ p, (if p ∈ A then LocNG.amp (R p.1) (d p) (LocNG.BBne (H := locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1)) else LocNG.amp (R p.1) (d p) (fun t => ¬ LocNG.BBne (H := locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1) t))‖ := by
  atlas_forward_decl GlobalTheory.HL.AmpLoc.global_amp_local
end
