import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleAtInertStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedPlacesDeclaredStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JointConditionAdm5Statement
import Development.AutomorphicArithmetic.CyclotomicBounds.SmallFacts
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.NEqRZeroMulXPow
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundAtPointAllLocalisationsOfObjectConditionsAl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCaseBoundAtPointOfAdmittedItems

section
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLink.BBSize

variable {D : D7}

theorem sum_locDeg_le (i : D.nd.Loc) (S : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (hS : ∀ v ∈ S, v ∈ placesOver D.host.E (D.nd.l i)) :
    ∑ w ∈ S, (locDeg D.host.E w : ℝ) ≤ 2 * D.R.f := by
  have hl := (D.nd.lPrime i).out
  refine le_trans ?_ (TwistedPlaces.sum_nLam_le D hl)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro v hv
    exact (Set.Finite.mem_toFinset _).2 (hS v hv)
  · intro v _ _
    positivity

theorem card_le_sum_locDeg (S : Finset (HeightOneSpectrum (𝓞 D.host.E))) :
    (S.card : ℝ) ≤ ∑ w ∈ S, (locDeg D.host.E w : ℝ) := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro v _
  exact_mod_cast TwistedPlaces.nLam_pos D v

theorem vdel_nonneg (i : D.nd.Loc) : (0 : ℝ) ≤ (D.nd.vdel i : ℝ) := by
  have : (0 : ℚ) ≤ D.nd.vdel i := by
    unfold NData.vdel
    positivity
  exact_mod_cast this

theorem vdel_le_two_t (i : D.nd.Loc) (h2 : D.nd.l i ∉ D.host.small) : (D.nd.vdel i : ℝ) ≤ 2 * D.R.t := by
  have := D.nd.lPrime i
  have h := LargeLevelLemmas.vdel_le i
  have hs : D.nd.s0 i = 1 := UpperTheory.Small.localLevel_eq_one_of_not_mem_smallPrimes D.nd i h2
  have hv : (padicValNat (D.nd.l i) D.R.t.factorial : ℚ) ≤ D.R.t := by
    exact_mod_cast padicValNat_factorial_le (D.nd.l i) D.R.t
  rw [hs] at h
  have : D.nd.vdel i ≤ 2 * (D.R.t : ℚ) := by
    push_cast at h
    linarith
  exact_mod_cast this

theorem blk_arith {f t n V large₂ c A k b v h : ℝ} (hf : 1 ≤ f) (ht : 1 ≤ t) (hn : 1 ≤ n) (hV : 1 ≤ V)
    (hL : 1 ≤ large₂) (hc : 1 ≤ c) (hA : A ≤ 6 * f) (hk0 : 0 ≤ k) (hk : k ≤ 2 * f) (hb0 : 0 ≤ b)
    (hb : b ≤ c * t * n * V * large₂) (hv0 : 0 ≤ v) (hv : v ≤ 2 * t) (hh : h ≤ c * t) :
    t * (A * b) + 4 * V * (k + 1) * v + t * k * h ≤ 32 * (c * f * n * t ^ 2 * V * large₂) := by
  have h1 : t * (A * b) ≤ 6 * (c * f * n * t ^ 2 * V * large₂) := by
    calc t * (A * b) ≤ t * ((6 * f) * (c * t * n * V * large₂)) := by gcongr
      _ = _ := by ring
  have h2 : 4 * V * (k + 1) * v ≤ 24 * (c * f * n * t ^ 2 * V * large₂) := by
    calc 4 * V * (k + 1) * v ≤ 4 * V * (3 * f) * (2 * t) := by gcongr; linarith
      _ = 24 * (1 * f * 1 * (t * 1) * V * 1) := by ring
      _ ≤ 24 * (c * f * n * (t * t) * V * large₂) := by gcongr
      _ = _ := by ring
  have h3 : t * k * h ≤ 2 * (c * f * n * t ^ 2 * V * large₂) := by
    calc t * k * h ≤ t * k * (c * t) := by gcongr
      _ ≤ t * (2 * f) * (c * t) := by gcongr
      _ = 2 * (c * f * 1 * t ^ 2 * 1 * 1) := by ring
      _ ≤ _ := by gcongr
  linarith

theorem col_arith {f t n V large₂ c A k m r v : ℝ} (hf : 1 ≤ f) (ht : 1 ≤ t) (hn : 1 ≤ n) (hV : 1 ≤ V)
    (hL : 1 ≤ large₂) (hc : 1 ≤ c) (hA : A ≤ 2 * f) (hk0 : 0 ≤ k) (hk : k ≤ 2 * f) (hm0 : 0 ≤ m) (hm : m ≤ t)
    (hr0 : 0 ≤ r) (hr : r ≤ t) (hv0 : 0 ≤ v) (hv : v ≤ 2 * t) :
    A * (m * v) + k * (2 * v + 2 * (c * r * n * V * large₂)) ≤ 16 * (c * f * n * t ^ 2 * V * large₂) := by
  have h1 : A * (m * v) ≤ 4 * (c * f * n * t ^ 2 * V * large₂) := by
    calc A * (m * v) ≤ (2 * f) * (t * (2 * t)) := by gcongr
      _ = 4 * (1 * f * 1 * t ^ 2 * 1 * 1) := by ring
      _ ≤ _ := by gcongr
  have h2 : k * (2 * v) ≤ 8 * (c * f * n * t ^ 2 * V * large₂) := by
    calc k * (2 * v) ≤ (2 * f) * (2 * (2 * t)) := by gcongr
      _ = 8 * (1 * f * 1 * (t * 1) * 1 * 1) := by ring
      _ ≤ 8 * (c * f * n * (t * t) * V * large₂) := by gcongr
      _ = _ := by ring
  have h3 : k * (2 * (c * r * n * V * large₂)) ≤ 4 * (c * f * n * t ^ 2 * V * large₂) := by
    calc k * (2 * (c * r * n * V * large₂)) ≤ (2 * f) * (2 * (c * t * n * V * large₂)) := by gcongr
      _ = 4 * (c * f * n * (t * 1) * V * large₂) := by ring
      _ ≤ 4 * (c * f * n * (t * t) * V * large₂) := by gcongr
      _ = _ := by ring
  rw [mul_add]
  linarith

theorem f_ge_one (D : D7) : (1 : ℝ) ≤ D.R.f := (TwistedPlaces.m_ge_one D).trans (TwistedPlaces.m_le_f D)

theorem nV_ge_one (D : D7) : (1 : ℝ) ≤ D.R.nV := by
  have := TwistedPlaces.t_ge_one D
  have h0 : (0 : ℝ) ≤ D.R.r := by positivity
  unfold Ranks.nV
  push_cast
  linarith

theorem blockBoundDeclaration_le_middleRange (L : SizeData₂ D) (i : D.nd.Loc) (h2 : D.nd.l i ∉ D.host.small) (dc : TruncatedSeriesCountingIdentities.Decl D i) (cB : ℕ) {c : ℝ}
    (hc : 1 ≤ c) (hB : (cB : ℝ) ≤ c * D.R.t * D.R.n * D.R.nV * TwistedPlaces.large₂ L)
    (hh : (h0 D.nd i dc.col : ℝ) ≤ c * D.R.t) :
    (KillingConditions.localErrorBoundDecomposition i dc cB : ℝ) ≤ 32 * (c * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * TwistedPlaces.large₂ L) := by
  have hrow := sum_locDeg_le i dc.row (fun v hv => (dc.cover v).1 (Or.inl hv))
  have hcol := sum_locDeg_le i dc.col (fun v hv => (dc.cover v).1 (Or.inr hv))
  have hr := card_le_sum_locDeg dc.row
  have hk := card_le_sum_locDeg dc.col
  have hA : ∑ w ∈ dc.row, ((locDeg D.host.E w : ℝ) + 2) ≤ 6 * D.R.f := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    linarith
  have := blk_arith (f_ge_one D) (TwistedPlaces.t_ge_one D) (TwistedPlaces.n_ge_one D) (nV_ge_one D) (TwistedPlaces.L_ge_one L) hc hA
    (Nat.cast_nonneg dc.col.card) (hk.trans hcol) (Nat.cast_nonneg cB) hB (vdel_nonneg i)
    (vdel_le_two_t i h2) hh
  unfold KillingConditions.localErrorBoundDecomposition
  push_cast
  rw [← Finset.sum_mul]
  exact this

theorem blockBoundAtZero_le_middleRange (L : SizeData₂ D) (i : D.nd.Loc) (h2 : D.nd.l i ∉ D.host.small)
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
    (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ) {c : ℝ}
    (hc : 1 ≤ c) (hB : (cB : ℝ) ≤ c * D.R.t * D.R.n * D.R.nV * TwistedPlaces.large₂ L)
    (hh : (h0 D.nd i dc.col : ℝ) ≤ c * D.R.t)
    (hu : ∀ u ∈ dc.col, (c0 u : ℝ) ≤ c * D.R.n * D.R.nV * TwistedPlaces.large₂ L ∧
      (Br.h0W i u ρ π : ℝ) ≤ c * D.R.r * D.R.n * D.R.nV * TwistedPlaces.large₂ L) :
    (localErrorBoundPlaces i ρ π dc c0 cB : ℝ) ≤ 48 * (c * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * TwistedPlaces.large₂ L) := by
  have hb := blockBoundDeclaration_le_middleRange L i h2 dc cB hc hB hh
  have hcol := sum_locDeg_le i dc.col (fun v hv => (dc.cover v).1 (Or.inr hv))
  have hk := card_le_sum_locDeg dc.col
  have hrt : (D.R.r : ℝ) ≤ D.R.t := by linarith [TwistedPlaces.t_ge D]
  have hmt : (D.R.m : ℝ) ≤ D.R.t := by linarith [TwistedPlaces.m_le_k D, TwistedPlaces.k_le_r D]
  have hc' := col_arith (f_ge_one D) (TwistedPlaces.t_ge_one D) (TwistedPlaces.n_ge_one D) (nV_ge_one D) (TwistedPlaces.L_ge_one L) hc hcol
    (Nat.cast_nonneg dc.col.card) (hk.trans hcol) (Nat.cast_nonneg D.R.m) hmt (Nat.cast_nonneg D.R.r) hrt
    (vdel_nonneg i) (vdel_le_two_t i h2)
  have hs : ∑ u ∈ dc.col, ((locDeg D.host.E u : ℝ) * (D.R.m : ℝ) * (D.nd.vdel i : ℝ) + 2 * (D.nd.vdel i : ℝ) +
        (Br.h0W i u ρ π : ℝ) + (D.R.r : ℝ) * (c0 u : ℝ)) ≤
      ∑ u ∈ dc.col, ((locDeg D.host.E u : ℝ) * ((D.R.m : ℝ) * (D.nd.vdel i : ℝ)) +
        (2 * (D.nd.vdel i : ℝ) + 2 * (c * D.R.r * D.R.n * D.R.nV * TwistedPlaces.large₂ L))) := by
    apply Finset.sum_le_sum
    intro u hu'
    obtain ⟨h1, h3⟩ := hu u hu'
    have h4 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) D.R.r)
    linarith
  rw [Finset.sum_add_distrib (f := fun u => (locDeg D.host.E u : ℝ) * ((D.R.m : ℝ) * (D.nd.vdel i : ℝ))),
    ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul] at hs
  unfold KillingConditions.localErrorBoundDecomposition at hb
  unfold localErrorBoundPlaces
  push_cast at hb ⊢
  linarith

theorem main : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (c : ℝ), 1 ≤ c → KillingConditions.DataAD L HW X R → KillingConditions.InvariantsBoundsWithCoarseColumnConstant L X c → KillingConditions.BBLe L X (60 * c) := by
  intro D L _ HW X R c hc hD hJ i hi hg hR π hπ
  obtain ⟨hB, hh, hS⟩ := hJ i hi hg hR
  have h2 : D.nd.l i ∉ D.host.small := fun h => hR.1 (Or.inl h)
  have hq : D.nd.l i ≠ D.host.q := fun h => hR.2.1 (Or.inl h)
  have hd : D.nd.l i ≠ D.host.d := fun h => hR.2.1 (Or.inr h)
  have hL := TwistedPlaces.L_ge_one L
  have hM0 : 0 ≤ c * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * TwistedPlaces.large₂ L := by
    have : 0 ≤ c := by linarith
    have : 0 ≤ TwistedPlaces.large₂ L := by linarith
    positivity
  have hM := le_mul_of_one_le_right hM0 hL
  have hE : 60 * c * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * (TwistedPlaces.large₂ L) ^ 2 =
      60 * (c * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * TwistedPlaces.large₂ L * TwistedPlaces.large₂ L) := by ring
  rw [hE]
  rcases TwistedPlaces.split_or_inert D h2 hq hd with hs | hin
  · rw [hD.error_bound_split_eq i hs π]
    have := blockBoundAtZero_le_middleRange L i h2 (X.ρ i) π (X.dc i) (X.c0 i) (X.cB i) hc hB hh
      (fun u hu => ⟨(hS hs u hu).1, (hS hs u hu).2 π hπ⟩)
    linarith
  · rw [hD.error_bound_inert_eq i hin π]
    have := blockBoundDeclaration_le_middleRange L i h2 (X.dc i) (X.cB i) hc hB hh
    linarith

end GlobalTheory.NLink.BBSize

end
end

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonPlacePart_localBound_le_middleRange : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (c : ℝ), 1 ≤ c → KillingConditions.DataAD L HW X R → KillingConditions.InvariantsBoundsWithCoarseColumnConstant L X c → KillingConditions.BBLe L X (60 * c) := by
  atlas_forward_decl GlobalTheory.NLink.BBSize.main
end

section
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem starAD_of_global : ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK),
    KillingConditions.DataAD L HW X R → KillingConditions.StepAD L X → TruncatedSeriesCountingIdentities.IntegralityFromMetric D →
    (∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
      (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i) (ep : Bool) (e' : ℕ)
      (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ), EmbeddingTypes.admitted i r ρ π dc ep e' c0 cB →
      (D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.admG2 i r ρ π) →
      EmbeddingTypes.aux₃ i r ρ π dc ep e' c0 cB) →
    (∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, TruncatedSeriesCountingIdentities.admG2 i (X.r i) (X.ρ i) π) →
    KillingConditions.KillAt X.ρ → TwistedPlaces.ShaFinOdd D →
    KillingConditions.StarAD L X := by
  classical
  intro D L HW X R hD hS h09 h78 hG2 hK hSha
  intro i hTw hg hR π hπ
  have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have hR' := hR
  obtain ⟨h23, hqd, -⟩ := hR'
  have hsm : D.nd.l i ∉ D.host.small := fun h => h23 (Or.inl h)
  have hl2 : D.nd.l i ≠ 2 := UpperTheory.Small.ne_two D.host hsm
  have hl3 : D.nd.l i ≠ 3 := fun h => h23 (Or.inr h)
  have hlq : D.nd.l i ≠ D.host.q := fun h => hqd (Or.inl h)
  have hld : D.nd.l i ≠ D.host.d := fun h => hqd (Or.inr h)
  have hg0 : D.nd.l i ≠ D.host.g 0 := fun h => hg (by simp [TwistedPlaces.gset, h])
  have hg1 : D.nd.l i ≠ D.host.g 1 := fun h => hg (by simp [TwistedPlaces.gset, h])
  have hZ : π ∈ D.nd.Z i := (D.Z_tie i π).2 ((D.Zgood_tie i π).1 hπ).1
  obtain ⟨hK1, hK2⟩ := hK i hTw
  obtain ⟨hFin, -⟩ := hK1 π hπ
  have hodd : Odd (D.nd.l i) := hl.odd_of_ne_two hl2
  have hShaT : ∀ e ∈ Finset.Ioo 0 D.R.t, GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤ := by
    intro e he
    rw [Finset.mem_Ioo] at he
    exact lt_top_iff_ne_top.2 (@hSha (D.nd.l i) (D.nd.lPrime i) e he.1 he.2)
  have hIco : Finset.Ico 1 D.R.t = Finset.Ioo 0 D.R.t := by
    ext e; simp only [Finset.mem_Ico, Finset.mem_Ioo]; omega
  have hVV : TwistedPlaces.VVr D (D.nd.l i) = ((∑ e ∈ Finset.Ioo 0 D.R.t, D.what₂.shaLen (D.nd.l i) e : ℚ) : ℝ) := by
    unfold TwistedPlaces.VVr
    simp only [Rows.Data.VV, hIco]
  have hcls : TwistedPlaces.SplitK D (D.nd.l i) ∨ TwistedPlaces.InertK D (D.nd.l i) := by
    unfold TwistedPlaces.SplitK TwistedPlaces.InertK Host.cls primeClass
    simp only [hsm, hlq, hld, if_false]
    split_ifs <;> simp
  rcases hcls with hsp | hin
  ·
    obtain ⟨ep, hdecl, hram, hAdm⟩ := hS.a78 i hTw hg hR hsp
    have hA := hAdm π hπ
    have hL : EmbeddingTypes.hypL i := ⟨hl.two_le, Or.inl hsp, fun _ => hram, hg0, hg1⟩
    have hzeta : ∀ v ∈ D.nd.Q i, D.nd.zeta i v ≠ 1 := fun v hv => (hA.2.2.2.2.2.1 v (Or.inr hv)).2.2.1 hv
    obtain ⟨-, -, hB⟩ := h78 i (X.r i) (X.ρ i) π (X.dc i) ep (X.eS i) (X.c0 i) (X.cB i) hA
      (fun _ _ _ => hG2 i hg π hπ) hL hdecl hZ
    have hT := hB hFin hShaT hzeta
    have hpl : (↑((X.dc i).row ∪ (X.dc i).col) : Set _) = placesOver D.host.E (D.nd.l i) := by
      ext v
      rw [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_coe]
      exact (X.dc i).cover v
    have hsum : TwistedPlaces.sumOver D (D.nd.l i) (X.len0 i π) =
        ((∑ u ∈ (X.dc i).col, (2 * (N.locDeg D.host.E u : ℚ) * D.R.m + 1) * (X.eS i : ℚ) : ℚ) : ℝ) := by
      unfold TwistedPlaces.sumOver
      rw [← hpl, finsum_mem_coe_finset]
      rw [Finset.sum_congr rfl fun w _ => hD.len0S i hsp π w]
      rw [← Rat.cast_sum]
      congr 1
      simp only [lenA]
      rw [Finset.sum_ite_mem, Finset.union_inter_cancel_right]
    have hBB := hD.error_bound_split_eq i hsp π
    have hcol : (∑ u ∈ (X.dc i).col,
        ((X.eS i : ℚ) + (N.locDeg D.host.E u : ℚ) * D.R.m * ((X.eS i : ℚ) + D.nd.vdel i) + 2 * D.nd.vdel i +
          Br.h0W i u (X.ρ i) π + (N.locDeg D.host.E u : ℚ) * D.R.m * (X.eS i : ℚ) + D.R.r * (X.c0 i u : ℚ))) =
        (∑ u ∈ (X.dc i).col, (2 * (N.locDeg D.host.E u : ℚ) * D.R.m + 1) * (X.eS i : ℚ)) +
        ∑ u ∈ (X.dc i).col, ((N.locDeg D.host.E u : ℚ) * D.R.m * D.nd.vdel i + 2 * D.nd.vdel i +
          Br.h0W i u (X.ρ i) π + D.R.r * (X.c0 i u : ℚ)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun u _ => by ring
    unfold EmbeddingTypes.boundSplit at hT
    rw [hcol] at hT
    have hT' := (Rat.cast_le (K := ℝ)).2 hT
    rw [hsum, hBB, hVV]
    unfold localErrorBoundPlaces TwistedPlaces.vhE
    push_cast at hT' hK2 ⊢
    linarith
  ·
    have hA := hS.a09 i hTw hg hR hin π hπ
    have hT := h09 i (X.r i) (X.ρ i) π (X.dc i) (X.lenRow i) (X.e' i) (X.cB i) (hS.goodR i) hA hg0 hg1 hZ hFin hShaT
    have hcol := hD.col i hin
    have hrow : (↑(X.dc i).row : Set _) = placesOver D.host.E (D.nd.l i) := by
      ext v
      have := (X.dc i).cover v
      rw [hcol] at this
      simpa using this
    have hsum : TwistedPlaces.sumOver D (D.nd.l i) (X.len0 i π) = ((∑ w ∈ (X.dc i).row, X.lenRow i w : ℚ) : ℝ) := by
      unfold TwistedPlaces.sumOver
      rw [← hrow, finsum_mem_coe_finset, Rat.cast_sum]
      exact Finset.sum_congr rfl fun w _ => hD.len0I i hin π w
    have hW : ∑ w ∈ (X.dc i).row ∪ (X.dc i).col, TruncatedSeriesCountingIdentities.lenW i (X.ρ i) π (X.dc i) (X.lenRow i) (X.e' i) w =
        ∑ w ∈ (X.dc i).row, X.lenRow i w := by
      rw [hcol, Finset.union_empty]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp [TruncatedSeriesCountingIdentities.lenW, hcol]
    rw [hW] at hT
    have hT' := (Rat.cast_le (K := ℝ)).2 hT
    rw [hsum, hD.error_bound_inert_eq i hin π, hVV]
    unfold KillingConditions.localErrorBoundDecomposition TwistedPlaces.vhE
    push_cast at hT' hK2 ⊢
    linarith

end GlobalTheory.NLink
end

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.starInequality_rowsAD_of_global_theorems : ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK), KillingConditions.DataAD L HW X R → KillingConditions.StepAD L X → TruncatedSeriesCountingIdentities.IntegralityFromMetric D → (∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i) (ep : Bool) (e' : ℕ) (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ), EmbeddingTypes.admitted i r ρ π dc ep e' c0 cB → (D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.admG2 i r ρ π) → EmbeddingTypes.aux₃ i r ρ π dc ep e' c0 cB) → (∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, TruncatedSeriesCountingIdentities.admG2 i (X.r i) (X.ρ i) π) → KillingConditions.KillAt X.ρ → TwistedPlaces.ShaFinOdd D → KillingConditions.StarAD L X := by
  atlas_forward_decl GlobalTheory.NLink.starAD_of_global
end

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem rowsAD_in_setting : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc)
    (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ),
    Setup L nch HW X C₂ → 1 ≤ C₂ → WachCoordinates.Conclusion2 D C₂ → KillingConditions.JointParametersHubConditions L HW X (rowC C₂) →
    KillingConditions.StarAD L X ∧ KillingConditions.BBLe L X 7200 := by
  intro hP D L P nch HW F Cm X C₂ hS hC hp2 hBCD
  have hstep : KillingConditions.StepAD L X :=
    { a09 := GlobalTheory.T.admissible_at_inert hP D L P nch HW F Cm X C₂ hS hC hp2 hBCD
      a78 := GlobalTheory.T.unramified_places_declared hP D L P nch HW F Cm X C₂ hS
      goodR := hS.canon.fam.good }
  have hst1 : TruncatedSeriesCountingIdentities.IntegralityFromMetric D := GlobalTheory.T.integralityFromMetric_of_designConditionAll hP.artin hP.bk hP.tate hP.euler D hS.facts.duties.2.2.1
  have h78 := GlobalTheory.T.splitCase_bound_at_point_of_admitted_items_alt hP.artin hP.tate hP.euler D
  have hG2 : ∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, TruncatedSeriesCountingIdentities.admG2 i (X.r i) (X.ρ i) π :=
    fun i hi π hπ => (GlobalTheory.T.set_point_good hP D L P nch HW F Cm X C₂ hS i hi π hπ).2.1
  refine ⟨GlobalTheory.T.starInequality_rowsAD_of_global_theorems D L HW X (rowC C₂) hS.canon.data hstep hst1 h78 hG2 hS.kill hS.sha, ?_⟩
  have h := GlobalTheory.T.nonPlacePart_localBound_le_middleRange D L P HW X (rowC C₂) 120 (by norm_num) hS.canon.data
    (GlobalTheory.T.joint_condition_adm5 hP D L P nch HW F Cm X C₂ hS)
  have e : (60 : ℝ) * 120 = 7200 := by norm_num
  rwa [e] at h

end GlobalTheory.NLink
end
