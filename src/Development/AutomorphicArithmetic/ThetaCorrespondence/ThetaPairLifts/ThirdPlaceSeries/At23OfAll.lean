import Development.AutomorphicArithmetic.ResidueCharacters.ClosedOfAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
import Development.AutomorphicArithmetic.ResidueCharacters.FamilyBoundAtTwoThreeOfLocalBounds
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NRowOn
import Development.AutomorphicArithmetic.ResidueCharacters.RowTwo
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConclusionSplitOfHub
import Development.AutomorphicArithmetic.ResidueCharacters.RowThree

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace UpperTheory.N
theorem mid_of_rowOn_alt (Q : D7 → ℕ → Prop)
    (hQ : ∀ D l, l.Prime → Q D l → D.host.condN.factorization l = D.host.QS.factorization l)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (h : _root_.UpperTheory.N.RowOnAlt Q A B) {eps : ℝ} (Fm : FamP eps) :
    ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x)
      (HW : HWOf (Fm.D x i).loc) (F : FonOf (Fm.D x i).loc (Fm.D x i).locA HW)
      (_ : CmpOf (Fm.D x i).loc (Fm.D x i).locA HW F) (X : KillingConditions.HubData (Fm.D x i)) (C₂ : ℝ),
      _root_.GlobalTheory.NLink.SetupAlt (Fm.L x i) (Fm.ex x hx i).nch HW X C₂ → ∀ k, TwistedPlaces.TwLoc (Fm.D x i) k → Q (Fm.D x i) ((Fm.D x i).nd.l k) →
        ∀ π ∈ (Fm.D x i).nd.Zgood k, Bd X.ρ k π (midF (Fm.L x i) C) := by
  obtain ⟨x0, h0⟩ := h Fm
  obtain ⟨C0, x1, hC0, hpar⟩ := GlobalTheory.T.admissible_parameters_family_const Fm
  refine ⟨18 * A * C0 + 2 * B * (3 * C0 + 9) + 5 * C0 + 1, max 3 (max x0 x1), ?_,
    fun x hxx hx i HW F Cm X C₂ hS k hTw hq π hπ => ?_⟩
  · have : 0 ≤ C0 := by linarith
    positivity
  have h3 : 3 ≤ x := (le_max_left _ _).trans hxx
  have hb := h0 x (((le_max_left _ _).trans (le_max_right _ _)).trans hxx) hx i HW F Cm X C₂ hS k hTw hq π hπ
  obtain ⟨-, -, -, hn, ht, -⟩ := hpar x (((le_max_right _ _).trans (le_max_right _ _)).trans hxx) hx i
  have hlog : 1 ≤ Real.log (Fm.L x i).sc.x := by
    rw [Fm.L_x x i hx, Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hl : ((Fm.D x i).nd.l k).Prime := ((Fm.D x i).nd.lPrime k).out
  have hc : costC (Fm.L x i) A B ((Fm.D x i).nd.l k) ≤
      midF (Fm.L x i) (18 * A * C0 + 2 * B * (3 * C0 + 9) + 5 * C0 + 1) :=
    Num.cost_le' (Fm.L x i) (Fm.params x hx i) hA hB hC0 hlog hn ht hl (hQ _ _ hl hq) le_rfl
  unfold Bd at hb ⊢
  linarith
theorem boundAtTwoThree_of_local_bounds_at_two_three (h3qd : ∀ D : D7, 3 ≠ D.host.q ∧ 3 ≠ D.host.d)
    (h2 : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ _root_.UpperTheory.N.SecondBoundCondition A B) (h3 : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ _root_.UpperTheory.N.ThirdBoundCondition A B)
    {eps : ℝ} (Fm : FamP eps) : _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm := by
  obtain ⟨A, B, hA, hB, h2⟩ := h2
  obtain ⟨A', B', hA', hB', h3⟩ := h3
  obtain ⟨C, x0, hC, h2⟩ := _root_.UpperTheory.N.mid_of_rowOn_alt (fun _ l => l = 2) (fun D l _ (e : l = 2) =>
    Num.factorization_condN D (by rw [e]; exact UpperTheory.Small.two_mem D.host)) A B hA hB (fun Fm => h2 Fm) Fm
  obtain ⟨C', x1, hC', h3⟩ := _root_.UpperTheory.N.mid_of_rowOn_alt (fun D l => l = 3 ∧ l ∉ D.host.small) (fun D l _ (e : l = 3 ∧ l ∉ D.host.small) =>
    Num.factorization_condN' D (by rw [e.1]; exact (h3qd D).1) (by rw [e.1]; exact (h3qd D).2)) A' B' hA' hB' (fun Fm => h3 Fm) Fm
  refine ⟨max C C', max x0 x1, fun x hxx hx i HW F Cm X C₂ hS k hTw hl π hπ => ?_⟩
  have h0 : 0 ≤ max C C' := hC.trans (le_max_left _ _)
  rcases hl with hl | hl
  · have h := h2 x ((le_max_left _ _).trans hxx) hx i HW F Cm X C₂ hS k hTw hl π hπ
    have h' := midF_mono (Fm.L x i) (le_max_left C C') h0
    unfold Bd at h ⊢; linarith
  · have h := h3 x ((le_max_right _ _).trans hxx) hx i HW F Cm X C₂ hS k hTw hl π hπ
    have h' := midF_mono (Fm.L x i) (le_max_right C C') h0
    unfold Bd at h ⊢; linarith
end UpperTheory.N
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
theorem UpperTheory.N.onAt_eq_two_bounds_of_setup (hP : Hypotheses₂) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc)
    (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ) (S : _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂) :
    UpperTheory.N.RowOnAt L X.ρ (fun l => l = 2) 6000 30000 := by
  intro i hTw h2 π hπ
  have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have hs : D.nd.l i ∈ D.host.small := by rw [show D.nd.l i = 2 from h2]; exact UpperTheory.Small.two_mem D.host
  have h4 : 2 ^ 2 ∣ D.host.QS := (pow_dvd_pow 2 (Nat.le_add_left 2 _)).trans D.host.tower_dvd
  have hgk : ∀ k, D.nd.l i ≠ D.host.g k := fun k e =>
    UpperTheory.Small.not_mem_of_mod D.host (D.ntypes.g_cond k) (e ▸ hs)
  have hg : D.nd.l i ∉ TwistedPlaces.gset D := by
    simp only [TwistedPlaces.gset, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hgk 0, hgk 1⟩
  have hL : EmbeddingTypes.hypL i := ⟨hl.two_le, Or.inr hs, fun h => absurd hs h, hgk 0, hgk 1⟩
  obtain ⟨dc, -, h⟩ := _root_.UpperTheory.N.conclusion_split_alt hP D L P nch HW F Cm X C₂ S i hg D.host.condN
    (UpperTheory.N.cycAt_of i fun _ => (h4.mul_right _).mul_right _) hL (UpperTheory.N.Two.decl_split D i h2)
    (UpperTheory.N.locAll hP D HW F Cm (D.nd.l i))
  obtain ⟨hB, hW, hz⟩ := h π hπ
  have hs2 : 2 ≤ D.nd.s0 i := by
    rw [D.nd.restNLevelExponent_of_two i h2]
    exact (Nat.prime_two.pow_dvd_iff_le_factorization D.host.QS_pos.ne').1 h4
  have hh := UpperTheory.N.h0_le D i dc.col (fun _ => hs2) (by omega) (fun u hu => (dc.cover u).1 (Or.inr hu))
  have hb := UpperTheory.N.Num.one_le_b L
  have hbB : L.sc.b ≤ RowSmall.hB L := (UpperTheory.N.Num.hB_bounds L P).1
  have hf : (⌊2 * L.sc.b⌋₊ : ℝ) ≤ 2 * L.sc.b := Nat.floor_le (by linarith)
  refine UpperTheory.N.bound_smallPrime_of_splitBound_cyclotomic L P X.ρ S.kill S.sha i hTw hs π hπ dc _ _ _ ?_ ?_ ?_ hW (by exact_mod_cast hh) hz hB
  · have : (Formalism.MainNotions.N.hN L : ℝ) ≤ RowSmall.hB L := Nat.floor_le (by
      show 0 ≤ RowSmall.hB L
      linarith)
    linarith
  · unfold GlobalTheory.HubX.hOf
    push_cast
    linarith
  · linarith
theorem UpperTheory.N.exists_nonneg_twoC_constants_of_prints : Hypotheses₂ → ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ _root_.UpperTheory.N.SecondBoundCondition A B :=
  fun hP => ⟨6000, 30000, by norm_num, by norm_num, fun Fm => ⟨0, fun x _ hx i HW F Cm X C₂ S =>
    _root_.UpperTheory.N.onAt_eq_two_bounds_of_setup hP _ _ (Fm.params x hx i) _ HW F Cm X C₂ S⟩⟩
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace UpperTheory.N
theorem rowThreeAt_of_setup_alt (hP : Hypotheses₂) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc)
    (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ) (S : _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂) :
    RowOnAt L X.ρ (fun l => l = 3 ∧ l ∉ D.host.small) 6000 30000 := by
  rintro i hTw ⟨h3, hs⟩ π hπ
  have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have h2 : D.nd.l i ≠ 2 := by omega
  have hq : D.nd.l i ≠ D.host.q := h3 ▸ (three_ne_q D).1
  have hd : D.nd.l i ≠ D.host.d := h3 ▸ (three_ne_q D).2
  have hgk : ∀ k, D.nd.l i ≠ D.host.g k := fun k => h3 ▸ three_ne_g D k
  have hg : D.nd.l i ∉ TwistedPlaces.gset D := by
    simp only [TwistedPlaces.gset, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hgk 0, hgk 1⟩
  have hle : D.nd.l i ≤ D.host.splitBound := by have := S.split; omega
  have hN : ¬ D.nd.l i ∣ D.host.condN := fun h => by
    rcases (D.host.dvd_condN_iff_small hl).1 h with h | h | h
    exacts [hs h, hq h, hd h]
  have hL : EmbeddingTypes.hypL i := ⟨hl.two_le, D.host.cls_splitK_or_small hl hle hq hd,
    fun _ v hv => GlobalTheory.HubLoc.ramIdx_eq_one D.host hl hN v hv, hgk 0, hgk 1⟩
  have hj : jacobiSym (-(D.host.d : ℤ)) (D.nd.l i) = 1 := D.host.split_small _ hl h2 hle
  obtain ⟨dc, -, h⟩ := _root_.UpperTheory.N.conclusion_split_alt hP D L P nch HW F Cm X C₂ S i hg D.host.condN
    (cycAt_of i fun e => absurd e h2) hL (decl_split D i h2 hj) (locAll hP D HW F Cm (D.nd.l i))
  obtain ⟨hB, hW, hz⟩ := h π hπ
  have hs0 : D.nd.s0 i = 1 := UpperTheory.Small.localLevel_eq_one_of_not_mem_smallPrimes D.nd i hs
  have hsl : D.nd.s0 i = RowSmall.sl D (D.nd.l i) := by
    unfold RowSmall.sl
    rw [hs0, Nat.factorization_eq_zero_of_not_dvd hN]; rfl
  have hh := h0_le D i dc.col (fun e => absurd e h2) hs0.ge (fun u hu => (dc.cover u).1 (Or.inr hu))
  have hb := Num.one_le_b L
  have hbB : L.sc.b ≤ RowSmall.hB L := (Num.hB_bounds L P).1
  have hf : (⌊2 * L.sc.b⌋₊ : ℝ) ≤ 2 * L.sc.b := Nat.floor_le (by linarith)
  refine bound_smallPrime_of_splitBound_cyclotomic_of_level_eq L P X.ρ S.kill S.sha i hTw hsl π hπ dc _ _ _ ?_ ?_ ?_ hW (by exact_mod_cast hh) hz hB
  · have : (Formalism.MainNotions.N.hN L : ℝ) ≤ RowSmall.hB L := Nat.floor_le (by
      show 0 ≤ RowSmall.hB L
      linarith)
    linarith
  · unfold GlobalTheory.HubX.hOf
    push_cast
    linarith
  · linarith
end UpperTheory.N
theorem UpperTheory.N.exists_nonneg_threeC_constants_of_prints : Hypotheses₂ → ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ _root_.UpperTheory.N.ThirdBoundCondition A B :=
  fun hP => ⟨6000, 30000, by norm_num, by norm_num, fun Fm => ⟨0, fun x _ hx i HW F Cm X C₂ S =>
    _root_.UpperTheory.N.rowThreeAt_of_setup_alt hP _ _ (Fm.params x hx i) _ HW F Cm X C₂ S⟩⟩
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace UpperTheory.N
theorem at23_family_alt (hP : Hypotheses₂) {eps : ℝ} (Fm : FamP eps) : _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm :=
  _root_.UpperTheory.N.boundAtTwoThree_of_local_bounds_at_two_three three_ne_q (_root_.UpperTheory.N.exists_nonneg_twoC_constants_of_prints hP) (_root_.UpperTheory.N.exists_nonneg_threeC_constants_of_prints hP) Fm
theorem boundAtTwoThree_n_linked (h : ∀ {eps : ℝ} (Fm : FamP eps), _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) :
    _root_.GlobalTheory.Fc.RL.LinkedAt p (fun Q L => _root_.GlobalTheory.Fc.R1.SlotNormCondition Q L fun 𝒞 => Closed 𝒞 fun Fm _ => _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm) :=
  _root_.GlobalTheory.Fc.RL.LinkedAt.of_row (GlobalTheory.Fc.Row.of_sel fun _ _ _ => closed_of_all _ fun Fm _ => h Fm)
theorem boundAtTwoThree_linked_of_recT (hP : Hypotheses₂) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) :
    _root_.GlobalTheory.Fc.RL.LinkedAt p (fun Q L => _root_.GlobalTheory.Fc.R1.SlotNormCondition Q L fun 𝒞 => Closed 𝒞 fun Fm _ => _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm) :=
  _root_.UpperTheory.N.boundAtTwoThree_n_linked (fun Fm => _root_.UpperTheory.N.at23_family_alt hP Fm) p
end UpperTheory.N
end
end
