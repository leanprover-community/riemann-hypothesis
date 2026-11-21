import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TwistStripLimits.BlockTypes
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PProjA
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.InfInd2Holds
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PAscAll
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpFin
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpTw
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PChord
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ProjOf
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceTens
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSlice
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PrHolds
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMap
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SqIntCritHolds
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.TopNeg

section
noncomputable section

open NumberField MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def Tr.Pos : {N : ℕ} → Tr E N → Prop
  | M, .leaf V _ => 0 < M ∧ IsDiscrete V
  | _, .node t₁ t₂ => Tr.Pos t₁ ∧ Tr.Pos t₂

theorem strip_shift (z : ℂ) {N : ℕ} (t : Tr E N) : (t.shift z).strip = t.strip := by
  induction t with
  | leaf V z' => rfl
  | node t₁ t₂ ih₁ ih₂ => simp only [Tr.shift, Tr.strip, ih₁, ih₂]

theorem twists_shift (z : ℂ) {N : ℕ} (t : Tr E N) : (t.shift z).twists = t.twists.map (· + z) := by
  induction t with
  | leaf V z' => rfl
  | node t₁ t₂ ih₁ ih₂ => simp only [Tr.shift, Tr.twists, ih₁, ih₂, List.map_append]

theorem length_twists_strip {N : ℕ} (t : Tr E N) : t.strip.twists.length = t.twists.length := by
  induction t with
  | leaf V z' => rfl
  | node t₁ t₂ ih₁ ih₂ => simp only [Tr.strip, Tr.twists, List.length_append, ih₁, ih₂]

theorem length_twists_of_strip {N : ℕ} {t t' : Tr E N} (h : t.strip = t'.strip) :
    t.twists.length = t'.twists.length := by
  rw [← length_twists_strip t, ← length_twists_strip t', h]

theorem pos_shift (z : ℂ) {N : ℕ} {t : Tr E N} (h : Tr.Pos t) : Tr.Pos (t.shift z) := by
  induction t with
  | leaf V z' => exact h
  | node t₁ t₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩

theorem allLeaves_shift (z : ℂ) {P : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} {N : ℕ} {t : Tr E N}
    (h : t.AllLeaves P) : (t.shift z).AllLeaves P := by
  induction t with
  | leaf V z' => exact h
  | node t₁ t₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩

theorem disc_of_pos {N : ℕ} {t : Tr E N} (h : Tr.Pos t) : t.Disc := by
  induction t with
  | leaf V z' => exact Or.inr h
  | node t₁ t₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩

theorem good_of_pos {N : ℕ} {t : Tr E N} (h : Tr.Pos t) (hz : ∀ z ∈ t.twists, z.re = 0) : t.Good := by
  induction t with
  | leaf V z' => exact Or.inr ⟨h.1, h.2, hz z' (by simp [Tr.twists])⟩
  | node t₁ t₂ ih₁ ih₂ =>
    exact ⟨ih₁ h.1 fun z hz' => hz z (by simp [Tr.twists, hz']),
      ih₂ h.2 fun z hz' => hz z (by simp [Tr.twists, hz'])⟩

theorem stable_of_pos {N : ℕ} {t : Tr E N} (h : Tr.Pos t) : t.AllLeaves fun _ V => IsStable V := by
  induction t with
  | leaf V z' => exact h.2.stable
  | node t₁ t₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩

theorem allLeaves_and {P Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} {N : ℕ} {t : Tr E N}
    (hP : t.AllLeaves P) (hQ : t.AllLeaves Q) : t.AllLeaves fun M V => P M V ∧ Q M V := by
  induction t with
  | leaf V z' => exact ⟨hP, hQ⟩
  | node t₁ t₂ ih₁ ih₂ => exact ⟨ih₁ hP.1 hQ.1, ih₂ hP.2 hQ.2⟩

theorem allLeaves_pos {N : ℕ} {t : Tr E N} (h : Tr.Pos t) : t.AllLeaves fun M _ => 0 < M := by
  induction t with
  | leaf V z' => exact h.1
  | node t₁ t₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩

theorem allLeaves_mono {P Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} (hPQ : ∀ M V, P M V → Q M V) {N : ℕ}
    {t : Tr E N} (h : t.AllLeaves P) : t.AllLeaves Q := by
  induction t with
  | leaf V z' => exact hPQ _ _ h
  | node t₁ t₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩

theorem getD_map_add (l : List ℂ) (z : ℂ) (i : ℕ) :
    (l.map (· + z)).getD i 0 = if i < l.length then l.getD i 0 + z else 0 := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none (not_lt.1 h)]

theorem getD_append (l l' : List ℂ) (i : ℕ) :
    (l ++ l').getD i 0 = if i < l.length then l.getD i 0 else l'.getD (i - l.length) 0 := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (not_lt.1 h)]

variable {N : ℕ}

theorem emb_trans {U U' : Submodule ℂ (Sm E N)} {P : Sm E N → Prop} (h₁ : Emb U (· ∈ U')) (h₂ : Emb U' P) : Emb U P := by
  obtain ⟨f₁, hf₁, hi₁, he₁⟩ := h₁
  obtain ⟨f₂, hf₂, hi₂, he₂⟩ := h₂
  refine ⟨f₂ ∘ₗ f₁, fun φ hφ => hf₂ _ (hf₁ φ hφ), fun φ hφ h0 => hi₁ φ hφ (hi₂ _ (hf₁ φ hφ) h0), fun o φ hφ => ?_⟩
  simp only [LinearMap.comp_apply]
  rw [he₁ o φ hφ, he₂ o _ (hf₁ φ hφ)]

theorem emb_of_isoV {V V' : Submodule ℂ (Sm E N)} (hV : IsStable V) (h : IsoV V V') : Emb V (· ∈ V') := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl V
  let p := Submodule.linearProjOfIsCompl V C hC
  have hp : ∀ φ (hφ : φ ∈ V), p φ = ⟨φ, hφ⟩ := fun φ hφ => Submodule.linearProjOfIsCompl_apply_left hC ⟨φ, hφ⟩
  refine ⟨V'.subtype ∘ₗ T.toLinearMap ∘ₗ p, fun φ hφ => by simp, fun φ hφ h0 => ?_, fun o φ hφ => ?_⟩
  · simp only [LinearMap.comp_apply, hp φ hφ, Submodule.subtype_apply, LinearEquiv.coe_coe,
      ZeroMemClass.coe_eq_zero, LinearEquiv.map_eq_zero_iff] at h0
    simpa using congrArg Subtype.val h0
  · have hψ : act o φ ∈ V := hV o φ hφ
    simp only [LinearMap.comp_apply, hp φ hφ, hp _ hψ, Submodule.subtype_apply, LinearEquiv.coe_coe]
    exact hT o ⟨φ, hφ⟩ ⟨act o φ, hψ⟩ rfl

theorem isoV_of_common {V₁ V₂ V' : Submodule ℂ (Sm E N)} (hV₂ : IsStable V₂) (h₁ : IsoV V₁ V') (h₂ : IsoV V₂ V') :
    IsoV V₁ V₂ := by
  obtain ⟨T₁, hT₁⟩ := h₁
  obtain ⟨T₂, hT₂⟩ := h₂
  refine ⟨T₁.trans T₂.symm, fun o φ ψ hψ => ?_⟩
  set χ := T₂.symm (T₁ φ) with hχ
  have hmem : act o χ.1 ∈ V₂ := hV₂ o χ.1 χ.2
  have key : T₂ ⟨act o χ.1, hmem⟩ = T₁ ψ := by
    apply Subtype.ext
    rw [hT₂ o χ ⟨act o χ.1, hmem⟩ rfl, hχ, LinearEquiv.apply_symm_apply, hT₁ o φ ψ hψ]
  simp only [LinearEquiv.trans_apply]
  rw [← key, LinearEquiv.symm_apply_apply]

theorem mulChi_absC_zero (φ : Sm E N) : mulChi N (Model.absC E 0) φ = φ :=
  Subtype.ext (funext fun g => by rw [mulChi_apply, ExponentTwist.chiDet_absC_val]; simp)

theorem tw_zero (V : Submodule ℂ (Sm E N)) : tw V 0 = V := by
  ext φ
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    simpa [mulChi_absC_zero] using hψ
  · intro hφ
    exact ⟨φ, hφ, mulChi_absC_zero φ⟩

theorem exists_subseq_const {α : Type*} {S : Set α} (hS : S.Finite) (f : ℕ → α) (hf : ∀ k, f k ∈ S) :
    ∃ a ∈ S, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ k, f (ψ k) = a := by
  have : ∃ a ∈ S, ∃ᶠ k in atTop, f k = a := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ᶠ k in atTop, ∀ a ∈ S, f k ≠ a := by
      have := (hS.eventually_all (l := atTop) (p := fun a k => f k ≠ a)).2
      exact this fun a ha => hcon a ha
    obtain ⟨k, hk⟩ := hall.exists
    exact hk (f k) (hf k) rfl
  obtain ⟨a, ha, hfr⟩ := this
  obtain ⟨ψ, hψ, hψa⟩ := Filter.extraction_of_frequently_atTop hfr
  exact ⟨a, ha, ψ, hψ, hψa⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5

end
end

section
noncomputable section

open NumberField MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem sum_map_add_const (m : Multiset ℂ) (w : ℂ) :
    (m.map (· + w)).sum = m.sum + (Multiset.card m : ℂ) * w := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, ih]
    push_cast
    ring

theorem norm_sum_le_of_le {M m : Multiset ℂ} {R : ℝ} (hle : M ≤ m) (hR : ∀ x ∈ m, ‖x‖ ≤ R) :
    ‖M.sum‖ ≤ Multiset.card M * R := by
  calc ‖M.sum‖ ≤ (M.map (fun x => ‖x‖)).sum := norm_multiset_sum_le M
    _ ≤ Multiset.card (M.map (fun x => ‖x‖)) • R := by
        refine Multiset.sum_le_card_nsmul _ _ ?_
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
        exact hR y (Multiset.subset_of_le hle hy)
    _ = Multiset.card M * R := by rw [Multiset.card_map, nsmul_eq_mul]

theorem side_bound {n : ℕ} (hn : 0 < n) (m m₁ : (E →+* ℂ) → Multiset ℂ) (w : ℂ) (R C : ℝ)
    (hcard : ∀ τ, Multiset.card (m₁ τ) = n) (hle : ∀ τ, (m₁ τ).map (· + w) ≤ m τ) (hR : ∀ τ, ∀ x ∈ m τ, ‖x‖ ≤ R)
    (hC : ‖∑ τ, (m₁ τ).sum‖ ≤ C) : ‖w‖ ≤ R + |C| ∧ ∀ τ, ∀ x ∈ m₁ τ, ‖x‖ ≤ 2 * R + |C| := by
  have hT : 0 < Fintype.card (E →+* ℂ) := Fintype.card_pos
  have h1 : ∀ τ, ‖((m₁ τ).map (· + w)).sum‖ ≤ n * R := fun τ => by
    have h := norm_sum_le_of_le (hle τ) (hR τ)
    rwa [Multiset.card_map, hcard τ] at h
  have h2 : ∑ τ, ((m₁ τ).map (· + w)).sum = ∑ τ, (m₁ τ).sum + ((Fintype.card (E →+* ℂ) * n : ℕ) : ℂ) * w := by
    simp only [sum_map_add_const, hcard, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    push_cast
    ring
  have h3 : ‖∑ τ, ((m₁ τ).map (· + w)).sum‖ ≤ Fintype.card (E →+* ℂ) * (n * R) := by
    calc ‖∑ τ, ((m₁ τ).map (· + w)).sum‖ ≤ ∑ τ, ‖((m₁ τ).map (· + w)).sum‖ := norm_sum_le _ _
      _ ≤ ∑ _τ : E →+* ℂ, (n * R : ℝ) := Finset.sum_le_sum fun τ _ => h1 τ
      _ = Fintype.card (E →+* ℂ) * (n * R) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hTn : (1 : ℝ) ≤ (Fintype.card (E →+* ℂ) * n : ℕ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hT.ne' hn.ne')
  have hw : ((Fintype.card (E →+* ℂ) * n : ℕ) : ℝ) * ‖w‖ ≤ ((Fintype.card (E →+* ℂ) * n : ℕ) : ℝ) * R + |C| := by
    have e : ((Fintype.card (E →+* ℂ) * n : ℕ) : ℂ) * w = ∑ τ, ((m₁ τ).map (· + w)).sum - ∑ τ, (m₁ τ).sum := by
      rw [h2]; ring
    have e2 := congrArg norm e
    rw [norm_mul, Complex.norm_natCast] at e2
    rw [e2]
    calc ‖∑ τ, ((m₁ τ).map (· + w)).sum - ∑ τ, (m₁ τ).sum‖
        ≤ ‖∑ τ, ((m₁ τ).map (· + w)).sum‖ + ‖∑ τ, (m₁ τ).sum‖ := norm_sub_le _ _
      _ ≤ Fintype.card (E →+* ℂ) * (n * R) + |C| := add_le_add h3 (hC.trans (le_abs_self C))
      _ = ((Fintype.card (E →+* ℂ) * n : ℕ) : ℝ) * R + |C| := by push_cast; ring
  have hwb : ‖w‖ ≤ R + |C| := by
    have hA := abs_nonneg C
    have hB : |C| ≤ ((Fintype.card (E →+* ℂ) * n : ℕ) : ℝ) * |C| := le_mul_of_one_le_left hA hTn
    by_contra hcon
    push_neg at hcon
    have := mul_lt_mul_of_pos_left hcon (lt_of_lt_of_le one_pos hTn)
    nlinarith
  refine ⟨hwb, fun τ x hx => ?_⟩
  have hxw : x + w ∈ m τ := Multiset.subset_of_le (hle τ) (Multiset.mem_map_of_mem _ hx)
  have hb := hR τ (x + w) hxw
  calc ‖x‖ = ‖(x + w) - w‖ := by rw [add_sub_cancel_right]
    _ ≤ ‖x + w‖ + ‖w‖ := norm_sub_le _ _
    _ ≤ R + (R + |C|) := add_le_add hb hwb
    _ = 2 * R + |C| := by ring

theorem block_bound {r s : ℕ} (hr : 0 < r) (hs : 0 < s) {V : Submodule ℂ (Sm E (r + s))} {V₁ : Submodule ℂ (Sm E r)}
    {V₂ : Submodule ℂ (Sm E s)} {z₁ z₂ : ℂ} {R C₁ C₂ : ℝ} (hV : IsDiscrete V) (hV₁ : IsDiscrete V₁)
    (hV₂ : IsDiscrete V₂) (hemb : Emb V (MemInd2 (tw V₁ z₁) (tw V₂ z₂))) (hR : InfBdd R V)
    (hC₁ : ∀ (U : Submodule ℂ (Sm E r)) (m : (E →+* ℂ) → Multiset ℂ), IsDiscrete U →
      (∀ τ, HasInfCharGL U τ (m τ)) → ‖∑ τ, (m τ).sum‖ ≤ C₁)
    (hC₂ : ∀ (U : Submodule ℂ (Sm E s)) (m : (E →+* ℂ) → Multiset ℂ), IsDiscrete U →
      (∀ τ, HasInfCharGL U τ (m τ)) → ‖∑ τ, (m τ).sum‖ ≤ C₂) :
    ‖z₁ - (s : ℂ) / 2‖ ≤ R + |C₁| ∧ ‖z₂ + (r : ℂ) / 2‖ ≤ R + |C₂| ∧
      InfBdd (2 * R + |C₁|) V₁ ∧ InfBdd (2 * R + |C₂|) V₂ := by
  have key : ∀ τ, ∃ m₁ m₂, HasInfCharGL V₁ τ m₁ ∧ HasInfCharGL V₂ τ m₂ ∧
      (m₁.map (· + (z₁ - (s : ℂ) / 2)) ≤ (hR τ).choose) ∧ (m₂.map (· + (z₂ + (r : ℂ) / 2)) ≤ (hR τ).choose) := by
    intro τ
    obtain ⟨m₁, m₂, h₁, h₂, he⟩ := infInd2_holds E r s V V₁ V₂ z₁ z₂ hV hV₁ hV₂ hemb τ _ (hR τ).choose_spec.1
    refine ⟨m₁, m₂, h₁, h₂, ?_, ?_⟩
    · rw [he]; exact Multiset.le_add_right _ _
    · rw [he]; exact Multiset.le_add_left _ _
  choose m₁ m₂ h₁ h₂ hl₁ hl₂ using key
  have hRb : ∀ τ, ∀ x ∈ (hR τ).choose, ‖x‖ ≤ R := fun τ => (hR τ).choose_spec.2
  obtain ⟨a₁, b₁⟩ := side_bound hr (fun τ => (hR τ).choose) m₁ (z₁ - (s : ℂ) / 2) R C₁ (fun τ => (h₁ τ).1) hl₁ hRb
    (hC₁ V₁ m₁ hV₁ h₁)
  obtain ⟨a₂, b₂⟩ := side_bound hs (fun τ => (hR τ).choose) m₂ (z₂ + (r : ℂ) / 2) R C₂ (fun τ => (h₂ τ).1) hl₂ hRb
    (hC₂ V₂ m₂ hV₂ h₂)
  exact ⟨a₁, a₂, fun τ => ⟨m₁ τ, h₁ τ, b₁ τ⟩, fun τ => ⟨m₂ τ, h₂ τ, b₂ τ⟩⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5

end
end

section
noncomputable section

open NumberField MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def Gap {N : ℕ} (ε : ℝ) (V : Submodule ℂ (Sm E N)) : Prop :=
  ∀ r, 0 < r → r < N → ∀ c ∈ ExpV r V, pE E N r c ≤ -ε * (r * ((N : ℝ) - r))

variable (E) in

def RepAll : Prop :=
  ∀ (M : ℕ) [MeasurableSpace (GA E M)] [BorelSpace (GA E M)] (ν : Measure (GA E M)) [ν.IsHaarMeasure]
    (K' : Subgroup (GL (Fin M) (Af E))) (W' : Submodule ℂ (Kinf E M → ℂ)) (R' : ℝ),
    IsOpen (K' : Set (GL (Fin M) (Af E))) → FiniteDimensional ℂ W' → Repro ν K' W' R'

def Concl {N : ℕ} (Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))) (Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E))))
    (V : ℕ → Submodule ℂ (Sm E N)) : Prop :=
  ∃ (φ : ℕ → ℕ) (t : ℕ → Tr E N) (t₀ : Tr E N), StrictMono φ ∧ Tr.Pos t₀ ∧ (∀ z ∈ t₀.twists, z.re = 0) ∧
    (∀ k, Tr.Pos (t k)) ∧ (∀ k, (t k).strip = t₀.strip) ∧
    t₀.AllLeaves (fun M V => ∃ K' ∈ Θ M, ∃ W' ∈ Ω M, HasType K' W' V) ∧
    (∀ i, Tendsto (fun k => ((t k).twists.getD i 0)) atTop (𝓝 (t₀.twists.getD i 0))) ∧
    ∀ k, Emb (V (φ k)) (· ∈ (t k).space)

def Seq (N : ℕ) (W : Submodule ℂ (Kinf E N → ℂ)) (K : Subgroup (GL (Fin N) (Af E)))
    (Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))) (Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) : Prop :=
  ∀ R : ℝ, 0 < N → RepAll E → ∀ V : ℕ → Submodule ℂ (Sm E N), (∀ k, IsDiscrete (V k)) → (∀ k, HasType K W (V k)) →
    (∀ k, InfBdd R (V k)) → Concl Ω Θ V

theorem concl_subseq {N : ℕ} {Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))}
    {Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))} {V : ℕ → Submodule ℂ (Sm E N)} {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    (h : Concl Ω Θ (V ∘ ψ)) : Concl Ω Θ V := by
  obtain ⟨φ, t, t₀, hφ, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨ψ ∘ φ, t, t₀, hψ.comp hφ, h1, h2, h3, h4, h5, h6, h7⟩

theorem seq_mono {N : ℕ} {W : Submodule ℂ (Kinf E N → ℂ)} {K : Subgroup (GL (Fin N) (Af E))}
    {Ω Ω' : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))} {Θ Θ' : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))}
    (h : Seq N W K Ω Θ) (hΩ : ∀ M, Ω M ⊆ Ω' M) (hΘ : ∀ M, Θ M ⊆ Θ' M) : Seq N W K Ω' Θ' := by
  intro R hN hRep V hVd hVt hVb
  obtain ⟨φ, t, t₀, hφ, h1, h2, h3, h4, h5, h6, h7⟩ := h R hN hRep V hVd hVt hVb
  exact ⟨φ, t, t₀, hφ, h1, h2, h3, h4, allLeaves_mono (fun M U ⟨K', hK', W', hW', hT⟩ =>
    ⟨K', hΘ M hK', W', hΩ M hW', hT⟩) h5, h6, h7⟩

theorem caseA (hFD : FinDisc) {N : ℕ} (hN : 0 < N) {K : Subgroup (GL (Fin N) (Af E))} {W : Submodule ℂ (Kinf E N → ℂ)}
    (hK : IsOpen (K : Set (GL (Fin N) (Af E)))) (hW : FiniteDimensional ℂ W)
    {Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))} {Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))}
    (hWΩ : W ∈ Ω N) (hKΘ : K ∈ Θ N) {R : ℝ} (hRep : RepAll E) {V : ℕ → Submodule ℂ (Sm E N)}
    (hVd : ∀ k, IsDiscrete (V k)) (hVt : ∀ k, HasType K W (V k)) (hVb : ∀ k, InfBdd R (V k)) {ε : ℝ} (hε : 0 < ε)
    (hfr : ∃ᶠ k in atTop, Gap ε (V k)) : Concl Ω Θ V := by
  letI : MeasurableSpace (GA E N) := borel _
  haveI : BorelSpace (GA E N) := ⟨rfl⟩
  haveI : LocallyCompactSpace (GA E N) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  obtain ⟨V₀, hV₀⟩ := hFD E N Measure.haar K W R ε hK hW hε (hRep N Measure.haar K W R hK hW)
  have hfr' : ∃ᶠ k in atTop, ∃ V' ∈ V₀, IsoV (V k) V' :=
    hfr.mono fun k hk => hV₀ (V k) (hVd k) (hVt k) (hVb k) hk
  have : ∃ V' ∈ V₀, ∃ᶠ k in atTop, IsoV (V k) V' := by
    by_contra hcon
    have hall : ∀ᶠ k in atTop, ∀ V' ∈ V₀, ¬ IsoV (V k) V' :=
      (Filter.eventually_all_finset V₀).2 fun V' hV' => Filter.not_frequently.1 fun h => hcon ⟨V', hV', h⟩
    obtain ⟨k, ⟨V', hV', hk⟩, hk'⟩ := (hfr'.and_eventually hall).exists
    exact hk' V' hV' hk
  obtain ⟨V', -, hfrV⟩ := this
  obtain ⟨ψ, hψ, hψV⟩ := Filter.extraction_of_frequently_atTop hfrV
  refine ⟨ψ, fun _ => .leaf (V (ψ 0)) 0, .leaf (V (ψ 0)) 0, hψ, ⟨hN, hVd _⟩, ?_, fun _ => ⟨hN, hVd _⟩,
    fun _ => rfl, ⟨K, hKΘ, W, hWΩ, hVt _⟩, fun i => tendsto_const_nhds, fun k => ?_⟩
  · intro z hz
    simp only [Tr.twists, List.mem_singleton] at hz
    simp [hz]
  · show Emb (V (ψ k)) (· ∈ tw (V (ψ 0)) 0)
    rw [tw_zero]
    exact emb_of_isoV (hVd _).stable (isoV_of_common (hVd _).stable (hψV k) (hψV 0))

theorem gap_of_le {N : ℕ} {V : Submodule ℂ (Sm E N)} {lam ε : ℝ} (h : Gap lam V) (hle : ε ≤ lam) : Gap ε V := by
  intro r hr hrN c hc
  have hpos : (0 : ℝ) < r * ((N : ℝ) - r) :=
    mul_pos (by exact_mod_cast hr) (sub_pos.2 (by exact_mod_cast hrN))
  have := h r hr hrN c hc
  nlinarith

theorem re_twists {r s : ℕ} (hr : 0 < r) (hs : 0 < s) {c : ℂ} {lam : ℝ}
    (h : pE E (r + s) r c = -lam * (r * s)) :
    (c / (r * (Module.finrank ℚ E : ℂ)) - (s : ℂ) / 2).re = -(s * lam) ∧
      (-c / (s * (Module.finrank ℚ E : ℂ)) + (r : ℂ) / 2).re = r * lam := by
  have hd : (0 : ℝ) < (Module.finrank ℚ E : ℝ) := by exact_mod_cast Module.finrank_pos
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  unfold pE at h
  push_cast at h
  have hc : c.re = (Module.finrank ℚ E : ℝ) * ((r : ℝ) * s / 2 - lam * (r * s)) := by
    field_simp at h ⊢; linarith
  have e1 : (r : ℂ) * (Module.finrank ℚ E : ℂ) = (((r : ℝ) * (Module.finrank ℚ E : ℝ) : ℝ) : ℂ) := by push_cast; ring
  have e2 : (s : ℂ) * (Module.finrank ℚ E : ℂ) = (((s : ℝ) * (Module.finrank ℚ E : ℝ) : ℝ) : ℂ) := by push_cast; ring
  have h2 : ((s : ℂ) / 2).re = (s : ℝ) / 2 := by simp
  have h3 : ((r : ℂ) / 2).re = (r : ℝ) / 2 := by simp
  constructor
  · rw [Complex.sub_re, e1, Complex.div_ofReal_re, h2, hc]
    field_simp; ring
  · rw [Complex.add_re, e2, Complex.div_ofReal_re, h3, Complex.neg_re, hc]
    field_simp; ring

end PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5

end
end

section
noncomputable section

open NumberField MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem caseB' (hTB : TwBound) (hNE : NodeEmb) (hG : Graft) (hTS : TwShift) (hTr : TrStable) {N : ℕ}
    {K : Subgroup (GL (Fin N) (Af E))} {W : Submodule ℂ (Kinf E N → ℂ)}
    {Ω Ωb : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))} {Θ Θb : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))}
    (hΩb : KTypes E Ωb) (hΘb : Levels E Θb)
    (hBTK : ∀ (r s : ℕ) (h : r + s = N) (V : Submodule ℂ (Sm E (r + s))) (V₁ : Submodule ℂ (Sm E r))
      (V₂ : Submodule ℂ (Sm E s)) (z₁ z₂ : ℂ), IsDiscrete V → IsDiscrete V₁ → IsDiscrete V₂ →
      HasType (h ▸ K) (h ▸ W) V → Emb V (MemInd2 (tw V₁ z₁) (tw V₂ z₂)) →
      (∃ K' ∈ Θb r, ∃ W' ∈ Ωb r, HasType K' W' V₁) ∧ (∃ K' ∈ Θb s, ∃ W' ∈ Ωb s, HasType K' W' V₂))
    (hIH : ∀ M < N, ∀ W' ∈ Ωb M, ∀ K' ∈ Θb M, Seq M W' K' Ω Θ)
    {R : ℝ} (hRep : RepAll E) {V : ℕ → Submodule ℂ (Sm E N)}
    (hVd : ∀ k, IsDiscrete (V k)) (hVt : ∀ k, HasType K W (V k)) (hVb : ∀ k, InfBdd R (V k))
    (hex : ∀ k, ∃ r, 0 < r ∧ r < N ∧ (ExpV r (V k)).Nonempty)
    (hsmall : ∀ ε > 0, ∀ᶠ k in atTop, ¬ Gap ε (V k)) : Concl Ω Θ V := by
  choose r c lam hr hrN hc hlam hpc hbd using
    fun k => PAscAll.exists_extremal (expFin_of dict_holds finTr_holds) expNeg_holds (V k) (hVd k) (hex k)
  have hlam0 : Tendsto lam atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun k => ha.trans (hlam k), fun a ha => ?_⟩
    filter_upwards [hsmall a ha] with k hk
    by_contra hle
    exact hk (gap_of_le (hbd k) (not_lt.1 hle))
  obtain ⟨r₀, hr₀N, σ₁, hσ₁, hσ₁r⟩ := exists_subseq_const (Set.finite_Iio N) r hrN
  have hr₀ : 0 < r₀ := hσ₁r 0 ▸ hr (σ₁ 0)
  have hr₀N' : r₀ < N := hr₀N
  obtain ⟨s, rfl⟩ : ∃ s, N = r₀ + s := ⟨N - r₀, by omega⟩
  have hs : 0 < s := by omega
  have hc' : ∀ k, c (σ₁ k) ∈ ExpV r₀ (V (σ₁ k)) := fun k => hσ₁r k ▸ hc (σ₁ k)
  have hpc' : ∀ k, pE E (r₀ + s) r₀ (c (σ₁ k)) = -lam (σ₁ k) * (r₀ * s) := fun k => by
    have h := hpc (σ₁ k)
    rw [hσ₁r k] at h
    rw [h]; push_cast; ring
  have hblk : ∀ k, ∃ (V₁ : Submodule ℂ (Sm E r₀)) (V₂ : Submodule ℂ (Sm E s)), IsDiscrete V₁ ∧ IsDiscrete V₂ ∧
      Emb (V (σ₁ k)) (MemInd2 (tw V₁ (c (σ₁ k) / (r₀ * (Module.finrank ℚ E : ℂ))))
        (tw V₂ (-c (σ₁ k) / (s * (Module.finrank ℚ E : ℂ))))) := fun k => by
    obtain ⟨T, hT⟩ := slice_of dict_holds finTr_holds E r₀ s hr₀ hs (V (σ₁ k)) (hVd _) _ (hc' k)
    have hL2 := chord_of expTw_holds sqIntCrit_holds E r₀ s hr₀ hs (V (σ₁ k)) _ T (lam (σ₁ k)) (hlam _) hT
      (hpc' k) (hbd (σ₁ k))
    exact proj_of pr_holds sliceTens_holds indMap_holds E r₀ s hr₀ hs (V (σ₁ k)) (hVd _) _ _ _ T hT hL2
  choose V₁ V₂ hV₁ hV₂ hemb using hblk
  let w₁ : ℕ → ℂ := fun k => c (σ₁ k) / (r₀ * (Module.finrank ℚ E : ℂ)) - (s : ℂ) / 2
  let w₂ : ℕ → ℂ := fun k => -c (σ₁ k) / (s * (Module.finrank ℚ E : ℂ)) + (r₀ : ℂ) / 2
  have hre : ∀ k, (w₁ k).re = -(s * lam (σ₁ k)) ∧ (w₂ k).re = r₀ * lam (σ₁ k) := fun k => re_twists hr₀ hs (hpc' k)
  obtain ⟨C₁, hC₁⟩ := hTB E r₀
  obtain ⟨C₂, hC₂⟩ := hTB E s
  have hbb := fun k => block_bound hr₀ hs (hVd (σ₁ k)) (hV₁ k) (hV₂ k) (hemb k) (hVb _) (hC₁ ·) (hC₂ ·)
  have hty := fun k => hBTK r₀ s rfl (V (σ₁ k)) (V₁ k) (V₂ k) _ _ (hVd _) (hV₁ k) (hV₂ k) (hVt _) (hemb k)
  choose K₁ hK₁ W₁ hW₁ hT₁ using fun k => (hty k).1
  choose K₂ hK₂ W₂ hW₂ hT₂ using fun k => (hty k).2
  obtain ⟨⟨⟨⟨a₁, b₁⟩, a₂⟩, b₂⟩, hmem, σ₂, hσ₂, hσ₂e⟩ :=
    exists_subseq_const ((((hΘb r₀).1.prod (hΩb r₀).1).prod (hΘb s).1).prod (hΩb s).1)
      (fun k => (((K₁ k, W₁ k), K₂ k), W₂ k)) (fun k => ⟨⟨⟨hK₁ k, hW₁ k⟩, hK₂ k⟩, hW₂ k⟩)
  simp only [Prod.mk.injEq] at hσ₂e
  obtain ⟨⟨⟨ma₁, mb₁⟩, ma₂⟩, mb₂⟩ := hmem
  obtain ⟨a, -, σ₃, hσ₃, ha⟩ := tendsto_subseq_of_bounded (x := fun j => (w₁ (σ₂ j), w₂ (σ₂ j)))
    (Metric.isBounded_closedBall (x := (0 : ℂ × ℂ)) (r := max (R + |C₁|) (R + |C₂|)))
    (fun j => by
      rw [mem_closedBall_zero_iff, Prod.norm_def]
      exact max_le_max (hbb _).1 (hbb _).2.1)
  let κ : ℕ → ℕ := fun j => σ₂ (σ₃ j)
  have hκ : StrictMono κ := hσ₂.comp hσ₃
  have ha₁ : Tendsto (fun j => w₁ (κ j)) atTop (𝓝 a.1) := (continuous_fst.tendsto a).comp ha
  have ha₂ : Tendsto (fun j => w₂ (κ j)) atTop (𝓝 a.2) := (continuous_snd.tendsto a).comp ha
  have hlamκ : Tendsto (fun j => lam (σ₁ (κ j))) atTop (𝓝 0) := hlam0.comp (hσ₁.comp hκ).tendsto_atTop
  have hre₁ : a.1.re = 0 := by
    have h1 : Tendsto (fun j => (w₁ (κ j)).re) atTop (𝓝 a.1.re) := (Complex.continuous_re.tendsto _).comp ha₁
    have h2 : Tendsto (fun j => (w₁ (κ j)).re) atTop (𝓝 0) := by
      have e : (fun j => (w₁ (κ j)).re) = fun j => -(s : ℝ) * lam (σ₁ (κ j)) := funext fun j => by
        rw [(hre (κ j)).1]; ring
      rw [e]; simpa using hlamκ.const_mul (-(s : ℝ))
    exact tendsto_nhds_unique h1 h2
  have hre₂ : a.2.re = 0 := by
    have h1 : Tendsto (fun j => (w₂ (κ j)).re) atTop (𝓝 a.2.re) := (Complex.continuous_re.tendsto _).comp ha₂
    have h2 : Tendsto (fun j => (w₂ (κ j)).re) atTop (𝓝 0) := by
      have e : (fun j => (w₂ (κ j)).re) = fun j => (r₀ : ℝ) * lam (σ₁ (κ j)) := funext fun j => (hre (κ j)).2
      rw [e]; simpa using hlamκ.const_mul (r₀ : ℝ)
    exact tendsto_nhds_unique h1 h2
  obtain ⟨φ₁, t₁, t₁₀, hφ₁, hp₁₀, hz₁₀, hp₁, hs₁, hl₁, htw₁, he₁⟩ :=
    hIH r₀ (by omega) b₁ mb₁ a₁ ma₁ (2 * R + |C₁|) hr₀ hRep (fun j => V₁ (κ j)) (fun j => hV₁ _)
      (fun j => by
        have e := hσ₂e (σ₃ j)
        rw [← e.1.1.1, ← e.1.1.2]
        exact hT₁ _)
      (fun j => (hbb _).2.2.1)
  obtain ⟨φ₂, t₂, t₂₀, hφ₂, hp₂₀, hz₂₀, hp₂, hs₂, hl₂, htw₂, he₂⟩ :=
    hIH s (by omega) b₂ mb₂ a₂ ma₂ (2 * R + |C₂|) hs hRep (fun j => V₂ (κ (φ₁ j))) (fun j => hV₂ _)
      (fun j => by
        have e := hσ₂e (σ₃ (φ₁ j))
        rw [← e.1.2, ← e.2]
        exact hT₂ _)
      (fun j => (hbb _).2.2.2)
  have hL₁ : ∀ j, (t₁ j).twists.length = t₁₀.twists.length := fun j => length_twists_of_strip (hs₁ j)
  have hL₂ : ∀ j, (t₂ j).twists.length = t₂₀.twists.length := fun j => length_twists_of_strip (hs₂ j)
  have hφ₁₂ : StrictMono fun j => φ₁ (φ₂ j) := hφ₁.comp hφ₂
  refine ⟨fun j => σ₁ (κ (φ₁ (φ₂ j))),
    fun j => .node ((t₁ (φ₂ j)).shift (w₁ (κ (φ₁ (φ₂ j))))) ((t₂ j).shift (w₂ (κ (φ₁ (φ₂ j))))),
    .node (t₁₀.shift a.1) (t₂₀.shift a.2), hσ₁.comp (hκ.comp hφ₁₂), ⟨pos_shift _ hp₁₀, pos_shift _ hp₂₀⟩, ?_,
    fun j => ⟨pos_shift _ (hp₁ _), pos_shift _ (hp₂ _)⟩, fun j => ?_,
    ⟨allLeaves_shift _ hl₁, allLeaves_shift _ hl₂⟩, fun i => ?_, fun j => ?_⟩
  · intro z hz
    simp only [Tr.twists, twists_shift, List.mem_append, List.mem_map] at hz
    rcases hz with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
    · simp [hz₁₀ y hy, hre₁]
    · simp [hz₂₀ y hy, hre₂]
  · simp only [Tr.strip, strip_shift, hs₁, hs₂]
  · simp only [Tr.twists, twists_shift, getD_append, getD_map_add, List.length_map, hL₁, hL₂]
    split_ifs with h1 h2
    · exact ((htw₁ i).comp hφ₂.tendsto_atTop).add (ha₁.comp hφ₁₂.tendsto_atTop)
    · exact (htw₂ (i - t₁₀.twists.length)).add (ha₂.comp hφ₁₂.tendsto_atTop)
    · exact tendsto_const_nhds
  · have hN := hNE E r₀ s (V (σ₁ (κ (φ₁ (φ₂ j))))) (V₁ (κ (φ₁ (φ₂ j)))) (V₂ (κ (φ₁ (φ₂ j)))) _ _ (hVd _) (hemb _)
    refine emb_trans hN ?_
    refine hG E r₀ s _ _ _ _ (ParabolicProjection.isStable_tw (hV₁ _).stable _)
      (hTr E r₀ _ (allLeaves_shift _ (stable_of_pos (hp₁ _)))) (ParabolicProjection.isStable_tw (hV₂ _).stable _)
      (hTr E s _ (allLeaves_shift _ (stable_of_pos (hp₂ _)))) ?_ ?_
    · exact hTS E r₀ (V₁ (κ (φ₁ (φ₂ j)))) (t₁ (φ₂ j)) _ (hV₁ _).stable (he₁ (φ₂ j))
    · exact hTS E s (V₂ (κ (φ₁ (φ₂ j)))) (t₂ j) _ (hV₂ _).stable (he₂ j)

end PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5

end
end

section
noncomputable section

open NumberField MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem caseB (hTB : TwBound) (hNE : NodeEmb) (hG : Graft) (hTS : TwShift) (hTr : TrStable) {N : ℕ}
    {K : Subgroup (GL (Fin N) (Af E))} {W : Submodule ℂ (Kinf E N → ℂ)}
    {Ω Ωb : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))} {Θ Θb : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))}
    (hΩb : KTypes E Ωb) (hΘb : Levels E Θb)
    (hBTK : ∀ (r s : ℕ) (h : r + s = N) (V : Submodule ℂ (Sm E (r + s))) (V₁ : Submodule ℂ (Sm E r))
      (V₂ : Submodule ℂ (Sm E s)) (z₁ z₂ : ℂ), IsDiscrete V → IsDiscrete V₁ → IsDiscrete V₂ →
      HasType (h ▸ K) (h ▸ W) V → Emb V (MemInd2 (tw V₁ z₁) (tw V₂ z₂)) →
      (∃ K' ∈ Θb r, ∃ W' ∈ Ωb r, HasType K' W' V₁) ∧ (∃ K' ∈ Θb s, ∃ W' ∈ Ωb s, HasType K' W' V₂))
    (hIH : ∀ M < N, ∀ W' ∈ Ωb M, ∀ K' ∈ Θb M, Seq M W' K' Ω Θ)
    {R : ℝ} (hRep : RepAll E) {V : ℕ → Submodule ℂ (Sm E N)}
    (hVd : ∀ k, IsDiscrete (V k)) (hVt : ∀ k, HasType K W (V k)) (hVb : ∀ k, InfBdd R (V k))
    (hsmall : ∀ ε > 0, ∀ᶠ k in atTop, ¬ Gap ε (V k)) : Concl Ω Θ V := by
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.1 (hsmall 1 one_pos)
  refine concl_subseq (ψ := fun k => k + k₁) (fun a b h => by simpa using h) ?_
  refine caseB' hTB hNE hG hTS hTr hΩb hΘb hBTK hIH hRep (fun k => hVd _) (fun k => hVt _) (fun k => hVb _)
    (fun k => ?_) (fun ε hε => (tendsto_add_atTop_nat k₁).eventually (hsmall ε hε))
  by_contra hcon
  apply hk₁ (k + k₁) (Nat.le_add_left _ _)
  intro r hr hrN c hc
  exact (hcon ⟨r, hr, hrN, c, hc⟩).elim

variable (E) in

def Q (N : ℕ) : Prop :=
  ∀ W : Submodule ℂ (Kinf E N → ℂ), FiniteDimensional ℂ W →
  ∃ Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)), KTypes E Ω ∧
  ∀ K : Subgroup (GL (Fin N) (Af E)), IsOpen (K : Set (GL (Fin N) (Af E))) →
  ∃ Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E))), Levels E Θ ∧ Seq N W K Ω Θ

theorem q_all (hFD : FinDisc) (hBT : BlockTypes) (hTB : TwBound) (hNE : NodeEmb) (hG : Graft) (hTS : TwShift)
    (hTr : TrStable) (N : ℕ) : Q E N := by
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro W hW
  obtain ⟨Ωb, hΩb, hBT'⟩ := hBT E N W hW
  have hI1 : ∀ (M' : ℕ) (W' : Submodule ℂ (Kinf E M' → ℂ)), ∃ Ω' : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)),
      M' < N → FiniteDimensional ℂ W' → KTypes E Ω' ∧ ∀ K' : Subgroup (GL (Fin M') (Af E)),
        IsOpen (K' : Set (GL (Fin M') (Af E))) → ∃ Θ' : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E))),
          Levels E Θ' ∧ Seq M' W' K' Ω' Θ' := by
    intro M' W'
    by_cases h : M' < N ∧ FiniteDimensional ℂ W'
    · obtain ⟨Ω', h1, h2⟩ := IH M' h.1 W' h.2
      exact ⟨Ω', fun _ _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ => ∅, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose ΩI hΩI using hI1
  refine ⟨fun M => {W' | ∃ h : N = M, W' = h ▸ W} ∪ ⋃ M' ∈ Set.Iio N, ⋃ W' ∈ Ωb M', ΩI M' W' M,
    fun M => ⟨?_, ?_⟩, fun K hK => ?_⟩
  · refine Set.Finite.union ?_ ((Set.finite_Iio N).biUnion fun M' hM' => (hΩb M').1.biUnion fun W' hW' =>
      ((hΩI M' W' hM' ((hΩb M').2 W' hW')).1 M).1)
    refine Set.Subsingleton.finite ?_
    rintro _ ⟨h₁, rfl⟩ _ ⟨h₂, rfl⟩
    rfl
  · rintro W' (⟨h, rfl⟩ | hW')
    · subst h
      exact hW
    · simp only [Set.mem_iUnion] at hW'
      obtain ⟨M', hM', W'', hW'', hmem⟩ := hW'
      exact ((hΩI M' W'' hM' ((hΩb M').2 W'' hW'')).1 M).2 W' hmem
  obtain ⟨Θb, hΘb, hBTK⟩ := hBT' K hK
  have hI2 : ∀ (M' : ℕ) (W' : Submodule ℂ (Kinf E M' → ℂ)) (K' : Subgroup (GL (Fin M') (Af E))),
      ∃ Θ' : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E))), M' < N → FiniteDimensional ℂ W' →
        IsOpen (K' : Set (GL (Fin M') (Af E))) → Levels E Θ' ∧ Seq M' W' K' (ΩI M' W') Θ' := by
    intro M' W' K'
    by_cases h : M' < N ∧ FiniteDimensional ℂ W' ∧ IsOpen (K' : Set (GL (Fin M') (Af E)))
    · obtain ⟨Θ', h1, h2⟩ := (hΩI M' W' h.1 h.2.1).2 K' h.2.2
      exact ⟨Θ', fun _ _ _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ => ∅, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
  choose ΘI hΘI using hI2
  refine ⟨fun M => {K' | ∃ h : N = M, K' = h ▸ K} ∪ ⋃ M' ∈ Set.Iio N, ⋃ W' ∈ Ωb M', ⋃ K' ∈ Θb M', ΘI M' W' K' M,
    fun M => ⟨?_, ?_⟩, ?_⟩
  · refine Set.Finite.union ?_ ((Set.finite_Iio N).biUnion fun M' hM' => (hΩb M').1.biUnion fun W' hW' =>
      (hΘb M').1.biUnion fun K' hK' => ((hΘI M' W' K' hM' ((hΩb M').2 W' hW') ((hΘb M').2 K' hK')).1 M).1)
    refine Set.Subsingleton.finite ?_
    rintro _ ⟨h₁, rfl⟩ _ ⟨h₂, rfl⟩
    rfl
  · rintro K' (⟨h, rfl⟩ | hK')
    · subst h
      exact hK
    · simp only [Set.mem_iUnion] at hK'
      obtain ⟨M', hM', W'', hW'', K'', hK'', hmem⟩ := hK'
      exact ((hΘI M' W'' K'' hM' ((hΩb M').2 W'' hW'') ((hΘb M').2 K'' hK'')).1 M).2 K' hmem
  intro R hN hRep V hVd hVt hVb
  by_cases hA : ∃ ε > 0, ∃ᶠ k in atTop, Gap ε (V k)
  · obtain ⟨ε, hε, hfr⟩ := hA
    exact caseA hFD hN hK hW (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩) hRep hVd hVt hVb hε hfr
  · have hB : ∀ ε > 0, ∀ᶠ k in atTop, ¬ Gap ε (V k) := fun ε hε =>
      Filter.not_frequently.1 fun h => hA ⟨ε, hε, h⟩
    refine caseB hTB hNE hG hTS hTr hΩb hΘb hBTK ?_ hRep hVd hVt hVb hB
    intro M' hM' W' hW' K' hK'
    refine seq_mono (hΘI M' W' K' hM' ((hΩb M').2 W' hW') ((hΘb M').2 K' hK')).2 (fun M x hx => ?_)
      (fun M x hx => ?_)
    · refine Or.inr ?_
      simp only [Set.mem_iUnion]
      exact ⟨M', hM', W', hW', hx⟩
    · refine Or.inr ?_
      simp only [Set.mem_iUnion]
      exact ⟨M', hM', W', hW', K', hK', hx⟩

theorem limit_of_finite_discrete (hFD : FinDisc) (hBT : BlockTypes) (hTB : TwBound) (hNE : NodeEmb) (hG : Graft) (hTS : TwShift)
    (hTr : TrStable) : Lim5 := by
  intro E _ _ _ N W hW
  obtain ⟨Ω, hΩ, h⟩ := q_all hFD hBT hTB hNE hG hTS hTr N W hW
  refine ⟨Ω, hΩ, fun K hK => ?_⟩
  obtain ⟨Θ, hΘ, hS⟩ := h K hK
  refine ⟨Θ, hΘ, ?_⟩
  intro _ _ μ _ R hN hRep V hVd hVt hVb
  obtain ⟨φ, t, t₀, hφ, hp₀, hz₀, hp, hs, hl, htw, he⟩ := hS R hN hRep V hVd hVt hVb
  exact ⟨φ, t, t₀, hφ, good_of_pos hp₀ hz₀, fun k => disc_of_pos (hp k), hs,
    allLeaves_and (allLeaves_pos hp₀) hl, htw, he⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5

end
end
