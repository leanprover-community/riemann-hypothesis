import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.WordSpan
import Development.WeilBound.CoreStatements.BranchingTraces.ExistsIntertwiner
import Development.WeilBound.CoreStatements.OrbitDecayEstimates.CurveDerivativeDecay.LipschitzEstimate
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.QminorInt
import Development.WeilBound.CoreStatements.BranchingTraces.ContinuousEmb

section
noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe.SM.LowWeightDensity

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition Formalism.FourierDecayAlt.P.CapelliAbstractCharacter CompanionTheory.D.DSIC

theorem signs {n : ℕ} {ε : Fin (n + 1) → Bool} {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool} {mu : Fin n → ℝ}
    {e : Fin n ⊕ Unit ≃ Fin (n + 1)} (hG : Gp ε lam ε' mu e) : (∃ a, ε' a = false) ∧ (∃ a, ε' a = true) := by
  obtain ⟨hfit, hε'⟩ := hG.fits
  have key0 : ∀ x, x ≠ zi e → ∃ c, x = e (Sum.inl c) := by
    intro x hx
    rcases hb : e.symm x with c | u
    · exact ⟨c, (Equiv.symm_apply_eq e).1 hb⟩
    · cases u
      exact absurd ((Equiv.symm_apply_eq e).1 hb) hx
  refine ⟨?_, ?_⟩
  · obtain ⟨a, ha⟩ := hG.neg
    by_cases hz : a = zi e
    · rw [hz, hfit] at ha
      exact absurd ha (by decide)
    · obtain ⟨c, rfl⟩ := key0 a hz
      exact ⟨c, by rw [← hε' c]; exact ha⟩
  · by_contra hno
    push_neg at hno
    have key : ∀ x, x ≠ zi e → ε x = false := by
      intro x hx
      obtain ⟨c, rfl⟩ := key0 x hx
      rw [hε' c]
      simpa using hno c
    have h1 : #{a : Fin (n + 1) | ε a = true} ≤ 1 := by
      apply Finset.card_le_one.2
      intro x hx y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      have hx2 : x = zi e := by
        by_contra h'
        rw [key x h'] at hx
        exact absurd hx (by decide)
      have hy2 : y = zi e := by
        by_contra h'
        rw [key y h'] at hy
        exact absurd hy (by decide)
      rw [hx2, hy2]
    have hsub : Finset.univ.erase (zi e) ⊆ Finset.filter (fun a => ε a = false) Finset.univ := by
      intro x hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact key x hx
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at h2
    have h3 := hG.le
    have h4 := hG.two
    simp only [Nat.add_sub_cancel] at h2
    omega

theorem exists_ds {m : ℕ} (ε : Fin m → Bool) (lam : Fin m → ℝ) (hm : 1 ≤ m) (hc : Formalism.QuantumDeterminants.IsHCParam lam)
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam (200 * (m : ℝ) ^ 3)) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)),
      IsDS ε lam σ := by
  have hq : (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) ≤ m := by
    have : ReciprocityTheory.ChartRestriction.DS.S7.q0 ε ≤ m := by
      unfold ReciprocityTheory.ChartRestriction.DS.S7.q0 ReciprocityTheory.ChartRestriction.DS.pOf
      exact (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans (by simp))
    exact_mod_cast this
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h2 : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  have h3 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 3 := by nlinarith
  have h4 : (8 * (m : ℝ)) * ReciprocityTheory.ChartRestriction.DS.S7.q0 ε ≤ (8 * (m : ℝ)) * m :=
    mul_le_mul_of_nonneg_left hq (by positivity)
  refine ReciprocityTheory.ChartRestriction.DS.G2.discrete_series_exists_large_gap m ε lam hc _ hg (Or.inr ?_)
  rw [max_lt_iff]
  constructor
  · nlinarith
  · nlinarith

theorem exists_ne {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)} (hσ : IsDS ε lam σ) : ∃ v ∈ lowKSub ε lam σ, v ≠ 0 := by
  obtain ⟨S0, hS0⟩ := hσ.2.2.2.2.2.1
  obtain ⟨v, hv, hv0, -⟩ := hS0.2.2.2.1
  have hle : S0 ≤ lowKSub ε lam σ := le_sSup (s := {S | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S}) hS0
  exact ⟨v, hle hv, hv0⟩

theorem exists_low {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)} (hσ : IsDS ε lam σ) : ∃ w ∈ lowKSub ε lam σ, ‖w‖ = 1 := by
  obtain ⟨v, hv, hv0⟩ := exists_ne hσ
  refine ⟨((‖v‖ : ℂ)⁻¹) • v, Submodule.smul_mem _ _ hv, ?_⟩
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
  rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hn]

theorem exists_P {n : ℕ} {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool} {e : Fin n ⊕ Unit ≃ Fin (n + 1)} {lam : Fin (n + 1) → ℝ}
    {mu : Fin n → ℝ} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] [CompleteSpace H'] {π : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → (H →L[ℂ] H)}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')} (hF : Fits ε ε' e) (hπ : IsDS ε lam π) (hσ : IsDS ε' mu σ)
    {j : H' →L[ℂ] H} (hj : j ≠ 0) (hjm : IsHMap ε' e π σ j) : ∃ P : H →L[ℂ] H', Intertw ε' e π σ P ∧ P ≠ 0 := by
  obtain ⟨-, -, hπU, -⟩ := hπ
  obtain ⟨-, -, hσU, -⟩ := hσ
  have memG : ∀ h : UJ ε', emb e (um h) ∈ PI.UpqRep.UJset ε := fun h =>
    PositivityTheory.UnitaryDecomposition.Com.emb_mem hF h.2
  have memH : ∀ h : UJ ε', um h ∈ PI.UpqRep.UJset ε' := fun h => h.2
  have embmul : ∀ A B : Matrix (Fin n) (Fin n) ℂ, emb e A * emb e B = emb e (A * B) := by
    intro A B
    simp only [emb, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp
  have emb1 : emb e 1 = 1 := by
    simp [emb]
  have huinv : ∀ h : UJ ε', um h * um h⁻¹ = 1 := by
    intro h
    simp [um]
  have hπinner : ∀ h : UJ ε', ∀ (u x : H),
      ⟪π (emb e (um h⁻¹)) u, x⟫_ℂ = ⟪u, π (emb e (um h)) x⟫_ℂ := by
    intro h u x
    have hmul := hπU.1.2 _ (memG h) _ (memG h⁻¹)
    rw [embmul, huinv, emb1, hπU.1.1] at hmul
    have hcomp : π (emb e (um h)) (π (emb e (um h⁻¹)) u) = u := by
      have h2 := congrArg (fun T : H →L[ℂ] H => T u) hmul
      simpa using h2.symm
    let L : H →ₗᵢ[ℂ] H := ⟨(π (emb e (um h))).toLinearMap, hπU.2.1 _ (memG h)⟩
    calc ⟪π (emb e (um h⁻¹)) u, x⟫_ℂ = ⟪L (π (emb e (um h⁻¹)) u), L x⟫_ℂ := (L.inner_map_map _ _).symm
      _ = ⟪u, π (emb e (um h)) x⟫_ℂ := by
        show ⟪π (emb e (um h)) (π (emb e (um h⁻¹)) u), π (emb e (um h)) x⟫_ℂ = _
        rw [hcomp]
  have hσinner : ∀ h : UJ ε', ∀ (y z : H'),
      ⟪σ (um h⁻¹) y, z⟫_ℂ = ⟪y, σ (um h) z⟫_ℂ := by
    intro h y z
    have hmul := hσU.1.2 _ (memH h) _ (memH h⁻¹)
    rw [huinv, hσU.1.1] at hmul
    have hcomp : σ (um h) (σ (um h⁻¹) y) = y := by
      have h2 := congrArg (fun T : H' →L[ℂ] H' => T y) hmul
      simpa using h2.symm
    let L : H' →ₗᵢ[ℂ] H' := ⟨(σ (um h)).toLinearMap, hσU.2.1 _ (memH h)⟩
    calc ⟪σ (um h⁻¹) y, z⟫_ℂ = ⟪L (σ (um h⁻¹) y), L z⟫_ℂ := (L.inner_map_map _ _).symm
      _ = ⟪y, σ (um h) z⟫_ℂ := by
        show ⟪σ (um h) (σ (um h⁻¹) y), σ (um h) z⟫_ℂ = _
        rw [hcomp]
  have hjn : ‖j‖ ≠ 0 := norm_ne_zero_iff.2 hj
  have hadj : ∀ (h : UJ ε') (x : H),
      ContinuousLinearMap.adjoint j (π (emb e (um h)) x) = σ (um h) (ContinuousLinearMap.adjoint j x) := by
    intro h x
    apply ext_inner_left ℂ
    intro y
    rw [ContinuousLinearMap.adjoint_inner_right, ← hπinner, ← hjm h⁻¹ y,
      ← ContinuousLinearMap.adjoint_inner_right, hσinner]
  refine ⟨((‖j‖ : ℂ)⁻¹) • ContinuousLinearMap.adjoint j, ⟨?_, ?_⟩, ?_⟩
  · rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, LinearIsometryEquiv.norm_map,
      inv_mul_cancel₀ hjn]
  · intro h x
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.map_smul, hadj]
  · intro h0
    have hc : ((‖j‖ : ℂ)⁻¹) ≠ 0 := inv_ne_zero (by exact_mod_cast hjn)
    have h1 : ContinuousLinearMap.adjoint j = 0 := by
      have := congrArg (fun T => ((‖j‖ : ℂ)) • T) h0
      simpa [smul_smul, hc] using this
    apply hj
    rw [← ContinuousLinearMap.adjoint_adjoint j, h1, map_zero]

theorem dense_sm {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)} {S : Submodule ℂ H} {E : Fin m → Fin m → Module.End ℂ S} (hm : 2 ≤ m)
    (hc : Formalism.QuantumDeterminants.IsHCParam lam) (hσ : IsDS ε lam σ) (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam (100 * (m : ℝ) ^ 3))
    (hS : IsSmMod ε σ S E) : Dense (S : Set H) := by
  obtain ⟨hcs, -, hU, hI, -, ⟨K, hK⟩, -⟩ := hσ
  haveI := hcs
  obtain ⟨v, hvK, hv0, -⟩ := hK.2.2.2.1
  have hvS : v ∈ S :=
    (hS.mem v).2 (CompanionTheory.D.gk.admitted.kFin_mem_smoothVecs m ε H σ hU hI v ⟨K, hK.1, hvK, hK.2.1⟩)
  have hstab : ∀ g ∈ PI.UpqRep.UJset ε, ∀ w ∈ S.topologicalClosure, σ g w ∈ S.topologicalClosure := by
    intro g hg w hw
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hw ⊢
    exact map_mem_closure (σ g).continuous hw (fun x hx => hS.stab g hg x hx)
  rcases hI S.topologicalClosure S.isClosed_topologicalClosure hstab with h | h
  · have hv' : v ∈ S.topologicalClosure := S.le_topologicalClosure hvS
    rw [h, Submodule.mem_bot] at hv'
    exact absurd hv' hv0
  · exact Submodule.dense_iff_topologicalClosure_eq_top.2 h

theorem one_le_hs' {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) (j : Fin m) : 1 ≤ hs (um g) := by
  exact ReciprocityTheory.ChartRestriction.DS.sigZeroDecay_one_le_hs g.2 j

theorem decay_low {n : ℕ} {ε' : Fin n → Bool} {mu : Fin n → ℝ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {σ : Matrix (Fin n) (Fin n) ℂ → (K →L[ℂ] K)} (hn : 1 ≤ n) (hc : Formalism.QuantumDeterminants.IsHCParam mu) (hσ : IsDS ε' mu σ)
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε' mu (200 * ((n : ℝ) + 1) ^ 3)) {w : K} (hw : w ∈ lowKSub ε' mu σ) (hw1 : ‖w‖ = 1) :
    Continuous (fun h : UJ ε' => conj ⟪w, σ (um h) w⟫_ℂ) ∧ ∃ C : ℝ, ∀ h : UJ ε',
      ‖conj ⟪w, σ (um h) w⟫_ℂ‖ ≤ C * hs (um h) ^ (-((n : ℝ) ^ 2 + 1 + (n : ℝ))) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨-, -, hU, -⟩ := hσ
    have h1 : Continuous (fun h : UJ ε' => um h) :=
      Units.continuous_val.comp continuous_subtype_val
    have hcont : Continuous (fun h : UJ ε' => σ (um h) w) :=
      (hU.2.2 w).comp_continuous h1 (fun h => h.2)
    exact (continuous_const.inner hcont).star
  · set N : ℕ := n ^ 2 + 1 + n with hN
    refine ⟨(Real.exp 1 * √(n : ℝ)) ^ (2 * N), fun h => ?_⟩
    have hA : 2 * N ≤ 12 * (n + 1) ^ 2 := by
      rw [hN]
      nlinarith
    have hb := CompanionTheory.Lime.T3.dec_low (N := n + 1) hn (by omega) hc hσ (by push_cast; exact hg) hw hw1
      (A := 2 * N) (by omega) hA h
    have hpos : 0 ≤ hs (um h) := le_trans zero_le_one (one_le_hs' h ⟨0, hn⟩)
    have hexp : ((n : ℝ) ^ 2 + 1 + n) = (N : ℝ) := by
      rw [hN]
      push_cast
      ring
    have key : (CompanionTheory.Lime.T3.nG h)⁻¹ ^ (2 * N) = hs (um h) ^ (-((n : ℝ) ^ 2 + 1 + n)) := by
      rw [pow_mul, inv_pow, CompanionTheory.Lime.T3.nG_sq, hexp, Real.rpow_neg hpos, Real.rpow_natCast, inv_pow]
    rw [RCLike.norm_conj, ← key]
    exact hb

end PositivityTheory.RgHe.SM.LowWeightDensity
end
end

section
noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe.SM

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition Formalism.FourierDecayAlt.P.CapelliAbstractCharacter CompanionTheory.D.DSIC

theorem signs {n : ℕ} {ε : Fin (n + 1) → Bool} {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool} {mu : Fin n → ℝ}
    {e : Fin n ⊕ Unit ≃ Fin (n + 1)} (hG : Gp ε lam ε' mu e) : (∃ a, ε' a = false) ∧ (∃ a, ε' a = true) := by apply LowWeightDensity.signs <;> assumption

theorem exists_ds {m : ℕ} (ε : Fin m → Bool) (lam : Fin m → ℝ) (hm : 1 ≤ m) (hc : Formalism.QuantumDeterminants.IsHCParam lam)
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam (200 * (m : ℝ) ^ 3)) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)),
      IsDS ε lam σ := by apply LowWeightDensity.exists_ds <;> assumption

theorem dense_sm {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)} {S : Submodule ℂ H} {E : Fin m → Fin m → Module.End ℂ S} (hm : 2 ≤ m)
    (hc : Formalism.QuantumDeterminants.IsHCParam lam) (hσ : IsDS ε lam σ) (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam (100 * (m : ℝ) ^ 3))
    (hS : IsSmMod ε σ S E) : Dense (S : Set H) := by apply LowWeightDensity.dense_sm <;> assumption

theorem exists_low {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)} (hσ : IsDS ε lam σ) : ∃ w ∈ lowKSub ε lam σ, ‖w‖ = 1 := by apply LowWeightDensity.exists_low <;> assumption

theorem exists_P {n : ℕ} {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool} {e : Fin n ⊕ Unit ≃ Fin (n + 1)} {lam : Fin (n + 1) → ℝ}
    {mu : Fin n → ℝ} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] [CompleteSpace H'] {π : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → (H →L[ℂ] H)}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')} (hF : Fits ε ε' e) (hπ : IsDS ε lam π) (hσ : IsDS ε' mu σ)
    {j : H' →L[ℂ] H} (hj : j ≠ 0) (hjm : IsHMap ε' e π σ j) : ∃ P : H →L[ℂ] H', Intertw ε' e π σ P ∧ P ≠ 0 := by apply LowWeightDensity.exists_P <;> assumption

theorem decay_low {n : ℕ} {ε' : Fin n → Bool} {mu : Fin n → ℝ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {σ : Matrix (Fin n) (Fin n) ℂ → (K →L[ℂ] K)} (hn : 1 ≤ n) (hc : Formalism.QuantumDeterminants.IsHCParam mu) (hσ : IsDS ε' mu σ)
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε' mu (200 * ((n : ℝ) + 1) ^ 3)) {w : K} (hw : w ∈ lowKSub ε' mu σ) (hw1 : ‖w‖ = 1) :
    Continuous (fun h : UJ ε' => conj ⟪w, σ (um h) w⟫_ℂ) ∧ ∃ C : ℝ, ∀ h : UJ ε',
      ‖conj ⟪w, σ (um h) w⟫_ℂ‖ ≤ C * hs (um h) ^ (-((n : ℝ) ^ 2 + 1 + (n : ℝ))) := by apply LowWeightDensity.decay_low <;> assumption

end PositivityTheory.RgHe.SM
end
end

section
noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe.SM.WordSpanNonVanishing

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition Formalism.FourierDecayAlt.P.CapelliAbstractCharacter CompanionTheory.D.DSIC PositivityTheory.UnitaryDecomposition.Com

theorem nonvan (hKey : KeyId) {N : ℕ} {ε : Fin (N + 2) → Bool} {ε' : Fin (N + 1) → Bool} {e : Fin (N + 1) ⊕ Unit ≃ Fin (N + 2)}
    {lam : Fin (N + 2) → ℝ} {mu : Fin (N + 1) → ℝ} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H'] {π : Matrix (Fin (N + 2)) (Fin (N + 2)) ℂ → (H →L[ℂ] H)}
    {σ : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ → (H' →L[ℂ] H')} {S : Submodule ℂ H} {E : Fin (N + 2) → Fin (N + 2) → Module.End ℂ S}
    {S' : Submodule ℂ H'} {E' : Fin (N + 1) → Fin (N + 1) → Module.End ℂ S'} {P : H →L[ℂ] H'} (hG : Gp ε lam ε' mu e)
    (hπ : IsDS ε lam π) (hσ : IsDS ε' mu σ) (hS : IsSmMod ε π S E) (hS' : IsSmMod ε' σ S' E') (hP : Intertw ε' e π σ P)
    (hP0 : P ≠ 0) (X : Dec ε' mu σ) (hκ : ∀ s, X.κ s = (mu s : ℂ) + (((N + 1 : ℕ) : ℂ) - 1) / 2) (j : Fin (N + 1))
    (hj : j ∈ X.S) (hwall : ∀ s, mu j - 1 / 2 ≠ lam s) : ∃ η ∈ S, X.p j (phi E e P η) ≠ 0 := by
  classical
  set ι : Fin (N + 1) → Fin (N + 2) := fun a => e (Sum.inl a) with hι
  set z : Fin (N + 2) := zi e with hz
  have hιinj : Function.Injective ι := fun a b h => Sum.inl_injective (e.injective h)
  have hιz : ∀ a, ι a ≠ z := by
    intro a h
    have := e.injective h
    simp at this
  have hPS : ∀ v : S, P v ∈ S' := fun v =>
    (hS'.mem _).2 (smooth_map hG.fits hP ((hS.mem _).1 v.2))
  let f : S →ₗ[ℂ] S' :=
    { toFun := fun v => ⟨P v, hPS v⟩
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro c x
        ext
        simp }
  have hfv : ∀ v : S, ((f v : S') : H') = P v := fun v => rfl
  have hf : ∀ (a b : Fin (N + 1)) (x : S), f (E (ι a) (ι b) x) = E' a b (f x) := by
    intro a b x
    ext
    rw [hfv, hS.act, hS'.act, hfv, ← blk_single e a b]
    exact dsigC_map hG.fits hP (fun X hX => (hS.real X hX x).differentiableAt) (single a b 1)
  set mπ : Fin (N + 2) → ℂ := fun s => (lam s : ℂ) - (((N + 2 : ℕ) : ℂ) - 1) / 2 with hmπ
  set mσ : Fin (N + 1) → ℂ := fun s => (mu s : ℂ) - (((N + 1 : ℕ) : ℂ) - 1) / 2 with hmσ
  have hcapπ : ∀ (u : ℂ) (v : S), qdet E u v = (∏ s, (u + mπ s)) • v := cap_of hG.hc hπ hS
  have hcapσ : ∀ (u : ℂ) (v : S'), qdet E' u v = (∏ s, (u + mσ s)) • v := cap_of hG.hc' hσ hS'
  have hw0 : ∀ y : S', qdet E' (-mσ j) y = 0 := by
    intro y
    rw [hcapσ, Finset.prod_eq_zero (Finset.mem_univ j) (by ring), zero_smul]
  set cG : ℂ := ∏ s, (-mσ j + 1 + mπ s) with hcGdef
  have hcG : cG ≠ 0 := by
    rw [hcGdef, Finset.prod_ne_zero_iff]
    intro s _ h
    apply hwall s
    have h' : -((mu j : ℂ) - (((N + 1 : ℕ) : ℂ) - 1) / 2) + 1 + ((lam s : ℂ) - (((N + 2 : ℕ) : ℂ) - 1) / 2) = 0 := h
    push_cast at h'
    have h2 : ((mu j - 1 / 2 : ℝ) : ℂ) = (lam s : ℂ) := by
      push_cast
      linear_combination -h'
    exact_mod_cast h2
  have hK : ∀ v : S, cG • f v = -∑ c : Fin (N + 1),
      (Th E' (-mσ j)) (fun l => f ((E (ι l) z) ((E z (ι c)) v))) c :=
    fun v => hKey S S' N E E' ι z f hS.gl hιinj hιz hf (-mσ j) cG (fun x => hcapπ _ x) hw0 v
  by_contra hno
  push_neg at hno
  let lift : (Fin (N + 1) → H') → Fin (N + 1) → S' := fun y l =>
    if h : y l ∈ S' then ⟨y l, h⟩ else 0
  have hlift : ∀ y ∈ SmT ε' σ, ∀ l, ((lift y l : S') : H') = y l := by
    intro y hy l
    simp [lift, (hS'.mem _).2 (hy l)]
  have hT0 : ∀ u : S, (Th E' (-mσ j)) (fun l => f ((E (ι l) z) u)) = 0 := by
    intro u
    set x : Fin (N + 1) → H' := phi E e P (u : H) with hxdef
    have hxl : ∀ l, x l = P ((E (ι l) z) u) := by
      intro l
      simp [hxdef, phi, ap, u.2, hι, hz]
    have hx : x ∈ SmT ε' σ := by
      intro l
      rw [hxl]
      exact (hS'.mem _).1 (hPS _)
    have hsum : ∑ t ∈ X.S, lift (X.p t x) = fun l => f ((E (ι l) z) u) := by
      funext l
      apply Subtype.ext
      rw [Finset.sum_apply, Submodule.coe_sum]
      have : ∀ t ∈ X.S, ((lift (X.p t x) l : S') : H') = X.p t x l :=
        fun t ht => hlift _ (X.p_sm t ht x hx) l
      rw [Finset.sum_congr rfl this, ← Finset.sum_apply, X.sum x hx, hxl, hfv]
    have heig : ∀ t ∈ X.S, (EE E') (lift (X.p t x)) = X.κ t • lift (X.p t x) := by
      intro t ht
      have hsm := X.p_sm t ht x hx
      funext c
      apply Subtype.ext
      have hcas := congrFun (X.cas t ht x hx) c
      simp only [casT, Pi.smul_apply] at hcas
      simp only [EE, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.coe_comp,
        Function.comp_apply, LinearMap.coe_proj, Function.eval, Pi.smul_apply, Submodule.coe_smul,
        Submodule.coe_sum]
      rw [hlift _ hsm c, ← hcas]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [hS'.act, hlift _ hsm l]
    have hκj : X.κ j = (N : ℂ) + mσ j := by
      rw [hκ j, hmσ]
      push_cast
      ring
    have hproj := th_proj hS'.gl hcapσ X.S (fun t => lift (X.p t x)) X.κ X.κ_inj heig hj j hκj
    rw [hsum] at hproj
    rw [hproj]
    have hpj : lift (X.p j x) = 0 := by
      rw [hno _ u.2]
      funext l
      simp [lift]
    rw [hpj, smul_zero]
  have hPv : ∀ v : S, P v = 0 := by
    intro v
    have h1 := hK v
    simp only [hT0, Pi.zero_apply, Finset.sum_const_zero, neg_zero] at h1
    have h2 : f v = 0 := (smul_eq_zero.1 h1).resolve_left hcG
    have h3 := congrArg (fun y : S' => (y : H')) h2
    simpa [hfv] using h3
  have hgap : Formalism.QuantumDeterminants.GapAtLeast ε lam (100 * ((N + 2 : ℕ) : ℝ) ^ 3) := by
    intro a b hab
    refine le_trans ?_ (hG.gap a b hab)
    push_cast
    have : (0 : ℝ) ≤ ((N : ℝ) + 2) ^ 3 := by positivity
    nlinarith
  have hdense : Dense (S : Set H) :=
    PositivityTheory.RgHe.SM.dense_sm (by omega) hG.hc hπ hgap hS
  apply hP0
  have heq := Continuous.ext_on hdense P.continuous (continuous_const (y := (0 : H')))
    (fun x hx => hPv ⟨x, hx⟩)
  ext x
  simpa using congrFun heq x

end PositivityTheory.RgHe.SM.WordSpanNonVanishing
end
end

section
noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe.SM.WordSpaces

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition Formalism.FourierDecayAlt.P.CapelliAbstractCharacter CompanionTheory.D.DSIC PositivityTheory.UnitaryDecomposition.Com PositivityTheory.RgHe.SM

section WS

variable {V : Type} [AddCommGroup V] [Module ℂ V] {m : ℕ} (E : Fin m → Fin m → Module.End ℂ V)

theorem one_mem_ws (L : ℕ) : (1 : Module.End ℂ V) ∈ wordSpan E L :=
  Submodule.subset_span ⟨[], by simp, by simp⟩

theorem gen_mem_ws (a b : Fin m) : E a b ∈ wordSpan E 1 :=
  Submodule.subset_span ⟨[(a, b)], by simp, by simp⟩

theorem ws_mul {L L' : ℕ} {T T' : Module.End ℂ V} (hT : T ∈ wordSpan E L) (hT' : T' ∈ wordSpan E L') :
    T * T' ∈ wordSpan E (L + L') := by
  have key : wordSpan E L * wordSpan E L' ≤ wordSpan E (L + L') := by
    unfold wordSpan
    rw [Submodule.span_mul_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨A, ⟨w, hw, rfl⟩, B, ⟨w', hw', rfl⟩, rfl⟩
    exact ⟨w ++ w', by simp only [List.length_append]; omega, by simp [List.map_append, List.prod_append]⟩
  exact key (Submodule.mul_mem_mul hT hT')

variable {k : ℕ} (F : Fin k → Fin k → Module.End ℂ V)

theorem tm_mem (hF : ∀ a b, F a b ∈ wordSpan E 1) (u : ℂ) (a b : Fin k) : Tm F u a b ∈ wordSpan E 1 := by
  unfold Tm
  refine Submodule.add_mem _ ?_ (hF a b)
  split_ifs
  · rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (one_mem_ws E 1)
  · exact Submodule.zero_mem _

theorem prod_mem_ws (l : List (Module.End ℂ V)) (h : ∀ x ∈ l, x ∈ wordSpan E 1) : l.prod ∈ wordSpan E l.length := by
  induction l with
  | nil => simpa using one_mem_ws E 0
  | cons x l ih =>
    rw [List.prod_cons, List.length_cons, add_comm]
    exact ws_mul E (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

theorem qminor_mem (hF : ∀ a b, F a b ∈ wordSpan E 1) {t : ℕ} (a b : Fin t → Fin k) (u : ℂ) :
    qminor F a b u ∈ wordSpan E t := by
  unfold qminor
  refine Submodule.sum_mem _ fun σ _ => ?_
  have h := prod_mem_ws E (List.ofFn fun i : Fin t => Tm F (u - (i : ℂ)) (a (σ i)) (b i)) (by
    intro x hx
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact tm_mem E F hF _ _ _)
  rw [List.length_ofFn] at h
  rw [← zsmul_eq_mul]
  exact zsmul_mem h _

end WS

theorem pj_words {N : ℕ} {ε : Fin (N + 2) → Bool} {ε' : Fin (N + 1) → Bool} {e : Fin (N + 1) ⊕ Unit ≃ Fin (N + 2)}
    {lam : Fin (N + 2) → ℝ} {mu : Fin (N + 1) → ℝ} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H'] {π : Matrix (Fin (N + 2)) (Fin (N + 2)) ℂ → (H →L[ℂ] H)}
    {σ : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ → (H' →L[ℂ] H')} {S : Submodule ℂ H} {E : Fin (N + 2) → Fin (N + 2) → Module.End ℂ S}
    {S' : Submodule ℂ H'} {E' : Fin (N + 1) → Fin (N + 1) → Module.End ℂ S'} {P : H →L[ℂ] H'} (hG : Gp ε lam ε' mu e)
    (hπ : IsDS ε lam π) (hσ : IsDS ε' mu σ) (hS : IsSmMod ε π S E) (hS' : IsSmMod ε' σ S' E') (hP : Intertw ε' e π σ P)
    (X : Dec ε' mu σ) (hκ : ∀ s, X.κ s = (mu s : ℂ) + (((N + 1 : ℕ) : ℂ) - 1) / 2) (j : Fin (N + 1)) (hj : j ∈ X.S) :
    ∃ R : Fin (N + 1) → Module.End ℂ S, (∀ l, R l ∈ wordSpan E (N + 1)) ∧
      ∀ ζ ∈ S, ∀ l, X.p j (phi E e P ζ) l = P (ap (R l) ζ) := by
  classical
  set ι : Fin (N + 1) → Fin (N + 2) := fun a => e (Sum.inl a) with hι
  set z : Fin (N + 2) := zi e with hz
  set m : Fin (N + 1) → ℂ := fun i => (mu i : ℂ) - (((N + 1 : ℕ) : ℂ) - 1) / 2 with hm
  have hq : ∀ u v, qdet E' u v = (∏ i, (u + m i)) • v := cap_of hG.hc' hσ hS'
  set w : ℂ := -m j with hw
  have hPs : ∀ v : S, P v ∈ S' := fun v => (hS'.mem _).2 (smooth_map hG.fits hP ((hS.mem _).1 v.2))
  let f : S →ₗ[ℂ] S' :=
    { toFun := fun v => ⟨P v, hPs v⟩
      map_add' := fun a b => Subtype.ext (by simp)
      map_smul' := fun c a => Subtype.ext (by simp) }
  have hf : ∀ a b (v : S), f (E (ι a) (ι b) v) = E' a b (f v) := fun a b v => Subtype.ext (by
    show P (E (ι a) (ι b) v : H) = (E' a b (f v) : H')
    rw [hS.act, hS'.act, ← blk_single (e := e)]
    exact dsigC_map hG.fits hP (fun X hX => (hS.real X hX v).differentiableAt) _)
  let co : (Fin (N + 1) → S') → Fin (N + 1) → H' := fun x l => x l
  have hco : ∀ x, co x ∈ SmT ε' σ := fun x l => (hS'.mem _).1 (x l).2
  let Y : (Fin (N + 1) → S') → X.S → Fin (N + 1) → S' := fun x t c =>
    ⟨X.p t (co x) c, (hS'.mem _).2 (X.p_sm t t.2 _ (hco x) c)⟩
  have hYe : ∀ x t, EE E' (Y x t) = X.κ t • Y x t := fun x t => funext fun c => Subtype.ext (by
    have := congrFun (X.cas t t.2 _ (hco x)) c
    rw [EE_apply, Submodule.coe_sum]
    simp only [hS'.act]
    exact this)
  have hYs : ∀ x, ∑ t, Y x t = x := fun x => funext fun c => Subtype.ext (by
    have := congrFun (X.sum _ (hco x)) c
    rw [Finset.sum_apply] at this
    rw [Finset.sum_apply, Submodule.coe_sum]
    exact (Finset.sum_coe_sort X.S fun t => X.p t (co x) c).trans this)
  set d : ℂ := ∏ i ∈ univ.erase j, (-m j + m i) with hd
  have hd0 : d ≠ 0 := by
    rw [hd, Finset.prod_ne_zero_iff]
    intro i hi h0
    have hne : i ≠ j := Finset.ne_of_mem_erase hi
    have : mu i = mu j := by
      have h1 : (mu i : ℂ) = mu j := by simp only [hm] at h0; linear_combination h0
      exact_mod_cast h1
    exact hne (hG.hc'.1.injective this)
  have hth : ∀ x, Th E' w x = d • Y x ⟨j, hj⟩ := fun x => by
    have h := th_proj hS'.gl hq univ (Y x) (fun t : X.S => X.κ t)
      (fun a _ b _ h => Subtype.ext (X.κ_inj a.2 b.2 h)) (fun t _ => hYe x t) (mem_univ (⟨j, hj⟩ : X.S)) j
      (by rw [hκ]; simp only [hm]; push_cast; ring)
    rwa [hYs] at h
  let T : Fin (N + 1) → Module.End ℂ S := fun l =>
    ∑ a : Fin (N + 1), ((-1 : ℂ) ^ ((a : ℕ) + (l : ℕ))) •
      (qminor (fun a b => E (ι a) (ι b)) a.succAbove l.succAbove w * E (ι a) z)
  refine ⟨fun l => d⁻¹ • T l, fun l => ?_, fun ζ hζ l => ?_⟩
  · refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_)
    exact ws_mul E (qminor_mem E _ (fun a b => gen_mem_ws E _ _) _ _ _) (gen_mem_ws E _ _)
  · set ζ' : S := ⟨ζ, hζ⟩
    let X0 : Fin (N + 1) → S := fun a => E (ι a) z ζ'
    let x : Fin (N + 1) → S' := fun c => f (X0 c)
    have hco' : co x = phi E e P ζ := funext fun c => by
      simp only [co, x, X0, phi, ap, dif_pos hζ]
      rfl
    have hT : T l ζ' = Th (fun a b => E (ι a) (ι b)) w X0 l := by
      rw [Th_apply]
      simp only [T, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
      rfl
    have h1 : P (ap (d⁻¹ • T l) ζ) = d⁻¹ • (f (Th (fun a b => E (ι a) (ι b)) w X0 l) : H') := by
      simp only [ap, dif_pos hζ, LinearMap.smul_apply, Submodule.coe_smul, map_smul]
      rw [hT]
      rfl
    have h2 := (thMap S S' N (fun a b => E (ι a) (ι b)) E' f hf w X0 l).1
    rw [h1, h2, show (fun l => f (X0 l)) = x from rfl, hth x, ← hco']
    simp only [Pi.smul_apply, Submodule.coe_smul, smul_smul, inv_mul_cancel₀ hd0, one_smul]
    rfl

end PositivityTheory.RgHe.SM.WordSpaces
end
end

section
noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe.SM

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition Formalism.FourierDecayAlt.P.CapelliAbstractCharacter CompanionTheory.D.DSIC

def wp {V : Type} [AddCommGroup V] [Module ℂ V] {m : ℕ} (E : Fin m → Fin m → Module.End ℂ V) (w : List (Fin m × Fin m)) :
    Module.End ℂ V :=
  (w.map fun p => E p.1 p.2).prod

theorem norm_entry_le {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) : ‖M i j‖ ≤ Real.sqrt (hs M) := by
  refine Real.le_sqrt_of_sq_le ?_
  unfold hs
  exact (Finset.single_le_sum (f := fun j => ‖M i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖ ^ 2) (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
      (Finset.mem_univ i))

theorem hs_nonneg' {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : 0 ≤ hs M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem um_inv_eq {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) : um g⁻¹ = Jm ε * (um g)ᴴ * Jm ε := by
  have hg : (um g)ᴴ * Jm ε * um g = Jm ε := g.2
  have e : um g * um g⁻¹ = 1 := by
    show ((g : (Matrix (Fin m) (Fin m) ℂ)ˣ) : Matrix (Fin m) (Fin m) ℂ) * (((g⁻¹ : UJ ε) : (Matrix (Fin m) (Fin m) ℂ)ˣ) : Matrix (Fin m) (Fin m) ℂ) = 1
    rw [Subgroup.coe_inv, Units.mul_inv]
  calc um g⁻¹ = Jm ε * Jm ε * um g⁻¹ := by rw [Jm_mul_self, Matrix.one_mul]
    _ = Jm ε * ((um g)ᴴ * Jm ε * um g) * um g⁻¹ := by rw [hg]
    _ = Jm ε * (um g)ᴴ * Jm ε * (um g * um g⁻¹) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [e, Matrix.mul_one]

theorem hs_inv' {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) : hs (um g⁻¹) = hs (um g) := by
  rw [um_inv_eq]
  unfold hs
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, norm_mul, norm_star]
  split_ifs <;> simp

theorem one_le_hs' {m : ℕ} {ε : Fin m → Bool} (hm : 1 ≤ m) (g : UJ ε) : 1 ≤ hs (um g) := by
  have j : Fin m := ⟨0, hm⟩
  have h := congrArg (fun M => ‖M j j‖) (show (um g)ᴴ * Jm ε * um g = Jm ε from g.2)
  have h1 : ‖Jm ε j j‖ = 1 := by simp only [Jm, Matrix.diagonal_apply_eq]; split_ifs <;> simp
  simp only [h1] at h
  have h2 : 1 ≤ ∑ i, ‖um g i j‖ ^ 2 := by
    rw [← h, Matrix.mul_apply]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [Jm, Matrix.mul_diagonal, norm_mul, norm_mul, Matrix.conjTranspose_apply, norm_star]
    split_ifs <;> simp [sq]
  exact h2.trans (Finset.sum_le_sum fun i _ =>
    Finset.single_le_sum (f := fun k => ‖um g i k‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j))

section Grow

variable {m : ℕ} {ε : Fin m → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)} {S : Submodule ℂ H} {E : Fin m → Fin m → Module.End ℂ S}

theorem inv_cancel' (hU : IsURepOn (UJset ε) σ) (g : UJ ε) (y : H) : σ (um g) (σ (um g⁻¹) y) = y := by
  have e : um g * um g⁻¹ = 1 := by
    show ((g : (Matrix (Fin m) (Fin m) ℂ)ˣ) : Matrix (Fin m) (Fin m) ℂ) * (((g⁻¹ : UJ ε) : (Matrix (Fin m) (Fin m) ℂ)ˣ) : Matrix (Fin m) (Fin m) ℂ) = 1
    rw [Subgroup.coe_inv, Units.mul_inv]
  have := hU.1.2 _ g.2 _ (g⁻¹).2
  rw [e, hU.1.1] at this
  exact (DFunLike.congr_fun this y).symm

theorem inv_cancel'' (hU : IsURepOn (UJset ε) σ) (g : UJ ε) (y : H) : σ (um g⁻¹) (σ (um g) y) = y := by
  have := inv_cancel' hU g⁻¹ y
  rwa [inv_inv] at this

theorem um_inv_inv (g : UJ ε) : (um g⁻¹)⁻¹ = um g := by
  rw [← um_inv, inv_inv]

theorem gen_step (hS : IsSmMod ε σ S E) (hU : IsURepOn (UJset ε) σ) (g : UJ ε) (v : S) (a b : Fin m) :
    (E a b ⟨σ (um g) v, hS.stab _ g.2 _ v.2⟩ : H) = ∑ c, ∑ d, (um g⁻¹ c a * um g b d) • σ (um g) (E c d v : H) := by
  have h := hS.conj (um g⁻¹) (g⁻¹).2 a b ⟨σ (um g) v, hS.stab _ g.2 _ v.2⟩ v (inv_cancel'' hU g v).symm
  rw [um_inv_inv] at h
  have h2 := congrArg (σ (um g)) h
  rw [inv_cancel' hU] at h2
  rw [h2, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_sum]
  exact Finset.sum_congr rfl fun d _ => map_smul _ _ _

theorem continuous_um : Continuous fun g : UJ ε => um g := Units.continuous_val.comp continuous_subtype_val

theorem continuous_um_inv : Continuous fun g : UJ ε => um g⁻¹ := continuous_um.comp continuous_inv

theorem word_growth (hS : IsSmMod ε σ S E) (hU : IsURepOn (UJset ε) σ) (w : List (Fin m × Fin m)) :
    ∀ v : S, Continuous (fun g : UJ ε => (wp E w ⟨σ (um g) v, hS.stab _ g.2 _ v.2⟩ : H)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ g : UJ ε, ‖(wp E w ⟨σ (um g) v, hS.stab _ g.2 _ v.2⟩ : H)‖ ≤ C * hs (um g) ^ w.length := by
  induction w using List.reverseRecOn with
  | nil =>
    intro v
    refine ⟨?_, ‖(v : H)‖, norm_nonneg _, fun g => ?_⟩
    · simp only [wp, List.map_nil, List.prod_nil, Module.End.one_apply]
      exact (hU.2.2 v).comp_continuous continuous_um fun g => g.2
    · simp only [wp, List.map_nil, List.prod_nil, Module.End.one_apply, List.length_nil, pow_zero, mul_one]
      exact le_of_eq (hU.2.1 _ g.2 v)
  | append_singleton w p ih =>
    intro v
    have e1 : ∀ g : UJ ε, (wp E (w ++ [p]) ⟨σ (um g) v, hS.stab _ g.2 _ v.2⟩ : H) =
        ∑ c, ∑ d, (um g⁻¹ c p.1 * um g p.2 d) • (wp E w ⟨σ (um g) (E c d v), hS.stab _ g.2 _ (E c d v).2⟩ : H) := by
      intro g
      have hx : E p.1 p.2 ⟨σ (um g) v, hS.stab _ g.2 _ v.2⟩ =
          ∑ c, ∑ d, (um g⁻¹ c p.1 * um g p.2 d) • (⟨σ (um g) (E c d v), hS.stab _ g.2 _ (E c d v).2⟩ : S) := by
        apply Subtype.ext
        rw [gen_step hS hU g v p.1 p.2, Submodule.coe_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Submodule.coe_sum]
        rfl
      simp only [wp, List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons, List.prod_nil,
        mul_one, Module.End.mul_apply]
      rw [hx, map_sum, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_sum, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [map_smul, Submodule.coe_smul]
    choose hc C hC0 hC using fun c d => ih (E c d v)
    refine ⟨?_, ∑ c, ∑ d, C c d, Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun d _ => hC0 c d, fun g => ?_⟩
    · simp only [e1]
      refine continuous_finsetSum _ fun c _ => continuous_finsetSum _ fun d _ => ?_
      refine Continuous.smul ?_ (hc c d)
      exact ((continuous_um_inv.matrix_elem c p.1).mul (continuous_um.matrix_elem p.2 d))
    · rw [e1]
      have hg1 : 0 ≤ hs (um g) := hs_nonneg' _
      have hco : ∀ c d, ‖um g⁻¹ c p.1 * um g p.2 d‖ ≤ hs (um g) := fun c d => by
        rw [norm_mul]
        have h1 := norm_entry_le (um g⁻¹) c p.1
        have h2 := norm_entry_le (um g) p.2 d
        rw [hs_inv'] at h1
        calc _ ≤ Real.sqrt (hs (um g)) * Real.sqrt (hs (um g)) :=
              mul_le_mul h1 h2 (norm_nonneg _) (Real.sqrt_nonneg _)
          _ = hs (um g) := Real.mul_self_sqrt hg1
      refine (norm_sum_le _ _).trans ?_
      rw [List.length_append, List.length_singleton, pow_succ, Finset.sum_mul]
      refine Finset.sum_le_sum fun c _ => (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun d _ => ?_
      rw [norm_smul]
      calc _ ≤ hs (um g) * (C c d * hs (um g) ^ w.length) :=
            mul_le_mul (hco c d) (hC c d g) (norm_nonneg _) hg1
        _ = _ := by ring

end Grow

section Span

variable {m : ℕ} {ε : Fin m → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)} {S : Submodule ℂ H} {E : Fin m → Fin m → Module.End ℂ S}

theorem ap_of_mem (T : Module.End ℂ S) {x : H} (hx : x ∈ S) : ap T x = (T ⟨x, hx⟩ : H) := by
  unfold ap; rw [dif_pos hx]

theorem ap_add (T₁ T₂ : Module.End ℂ S) (x : H) : ap (T₁ + T₂) x = ap T₁ x + ap T₂ x := by
  unfold ap; split_ifs <;> simp

theorem ap_smul (c : ℂ) (T : Module.End ℂ S) (x : H) : ap (c • T) x = c • ap T x := by
  unfold ap; split_ifs <;> simp

theorem ap_zero (x : H) : ap (0 : Module.End ℂ S) x = 0 := by
  unfold ap; split_ifs <;> simp

theorem span_growth (hm : 1 ≤ m) (hS : IsSmMod ε σ S E) (hU : IsURepOn (UJset ε) σ) (L : ℕ) (T : Module.End ℂ S)
    (hT : T ∈ wordSpan E L) : ∀ v : S, Continuous (fun g : UJ ε => ap T (σ (um g) v)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ g : UJ ε, ‖ap T (σ (um g) v)‖ ≤ C * hs (um g) ^ L := by
  induction hT using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    intro v
    obtain ⟨hc, C, hC0, hC⟩ := word_growth hS hU w v
    refine ⟨?_, C, hC0, fun g => ?_⟩
    · have e : (fun g : UJ ε => ap (wp E w) (σ (um g) v)) =
          fun g => (wp E w ⟨σ (um g) v, hS.stab _ g.2 _ v.2⟩ : H) := funext fun g => ap_of_mem _ _
      change Continuous (fun g : UJ ε => ap (wp E w) (σ (um g) v))
      rw [e]
      exact hc
    · rw [ap_of_mem _ (hS.stab _ g.2 _ v.2)]
      exact (hC g).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_le_hs' hm g) hw) hC0)
  | zero =>
    intro v
    refine ⟨?_, 0, le_rfl, fun g => ?_⟩
    · simp only [ap_zero]; exact continuous_const
    · simp [ap_zero]
  | add x y _ _ hx hy =>
    intro v
    obtain ⟨h1, C1, hC1, hb1⟩ := hx v
    obtain ⟨h2, C2, hC2, hb2⟩ := hy v
    refine ⟨?_, C1 + C2, add_nonneg hC1 hC2, fun g => ?_⟩
    · simp only [ap_add]; exact h1.add h2
    · rw [ap_add, add_mul]; exact (norm_add_le _ _).trans (add_le_add (hb1 g) (hb2 g))
  | smul c x _ hx =>
    intro v
    obtain ⟨h1, C1, hC1, hb1⟩ := hx v
    refine ⟨?_, ‖c‖ * C1, mul_nonneg (norm_nonneg _) hC1, fun g => ?_⟩
    · simp only [ap_smul]; exact h1.const_smul c
    · rw [ap_smul, norm_smul, mul_assoc]; exact mul_le_mul_of_nonneg_left (hb1 g) (norm_nonneg _)

theorem span_adj (hS : IsSmMod ε σ S E) (L : ℕ) (T : Module.End ℂ S) (hT : T ∈ wordSpan E L) :
    ∃ T' : Module.End ℂ S, ∀ x y : S, ⟪(y : H), (T x : H)⟫_ℂ = ⟪(T' y : H), (x : H)⟫_ℂ := by
  have gen : ∀ a b, ∀ x y : S, ⟪(y : H), (E a b x : H)⟫_ℂ = ⟪(((sgn ε a b : ℂ) • E b a y : S) : H), (x : H)⟫_ℂ := by
    intro a b x y
    have h := hS.unit a b x y
    rw [← inner_conj_symm, ← Submodule.coe_inner, h, map_mul, Submodule.coe_smul, inner_smul_left, Complex.conj_ofReal,
      inner_conj_symm, Submodule.coe_inner]
  have word : ∀ w : List (Fin m × Fin m), ∃ T' : Module.End ℂ S, ∀ x y : S,
      ⟪(y : H), (wp E w x : H)⟫_ℂ = ⟪(T' y : H), (x : H)⟫_ℂ := by
    intro w
    induction w with
    | nil => exact ⟨1, fun x y => by simp [wp]⟩
    | cons p w ih =>
      obtain ⟨T', hT'⟩ := ih
      refine ⟨T' * ((sgn ε p.1 p.2 : ℂ) • E p.2 p.1), fun x y => ?_⟩
      simp only [wp, List.map_cons, List.prod_cons, Module.End.mul_apply] at hT' ⊢
      rw [gen, hT']
      rfl
  induction hT using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, -, rfl⟩ := hx
    exact word w
  | zero => exact ⟨0, fun x y => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨T1, h1⟩ := hx
    obtain ⟨T2, h2⟩ := hy
    exact ⟨T1 + T2, fun a b => by simp [h1, h2]⟩
  | smul c x _ hx =>
    obtain ⟨T1, h1⟩ := hx
    exact ⟨(starRingEnd ℂ c) • T1, fun a b => by
      simp only [LinearMap.smul_apply, Submodule.coe_smul, inner_smul_right, inner_smul_left, h1, Complex.conj_conj]⟩

end Span

section ZeroSec

variable {n : ℕ} {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool} {e : Fin n ⊕ Unit ≃ Fin (n + 1)}

theorem hs_emb (M : Matrix (Fin n) (Fin n) ℂ) : hs (emb e M) = hs M + 1 := by
  unfold hs emb
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [← Equiv.sum_comp e]
  simp only [Equiv.symm_apply_apply]
  have : ∀ x : Fin n ⊕ Unit, ∑ j, ‖Matrix.fromBlocks M 0 0 (1 : Matrix Unit Unit ℂ) x (e.symm j)‖ ^ 2 =
      ∑ y, ‖Matrix.fromBlocks M 0 0 (1 : Matrix Unit Unit ℂ) x y‖ ^ 2 := fun x => by
    rw [← Equiv.sum_comp e]; simp only [Equiv.symm_apply_apply]
  simp [this, Fintype.sum_sum_type]

theorem continuous_embU (hF : Fits ε ε' e) : Continuous (embU hF) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact continuous_emb
  · exact continuous_emb.comp continuous_inv

theorem continuous_hs_um {m : ℕ} {ε₀ : Fin m → Bool} : Continuous fun g : UJ ε₀ => hs (um g) := by
  unfold hs
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    ((continuous_um.matrix_elem i j).norm).pow 2

theorem zero_proof : Zero := by
  intro n ε ε' e H _ _ _ π S E hF hn hS hU hD ν hν c L C hc hcb hzero T hT η b
  have := hν
  have hn1 : 1 ≤ n + 1 := by omega
  obtain ⟨hFc, CT, hCT0, hCT⟩ := span_growth hn1 hS hU L T hT η
  have hIntR := CompanionTheory.Lime.T3.analytic_estimates.2.2.1
  set a : ℝ := (n : ℝ) ^ 2 + 1 with ha
  set C' : ℝ := max C 0 with hC'
  have hcb' : ∀ h, ‖c h‖ ≤ C' * hs (um h) ^ (-(a + L)) := fun h =>
    (hcb h).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (hs_nonneg' _) _))
  set K₀ : ℝ := C' * CT * 2 ^ L with hK₀
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hK₀0 : 0 ≤ K₀ := mul_nonneg (mul_nonneg hC'0 hCT0) (by positivity)

  have hX : ∀ h : UJ ε', ‖ap T (π (emb e (um h)) η)‖ ≤ CT * 2 ^ L * hs (um h) ^ L := fun h => by
    have h1 := hCT (embU hF h)
    have h2 : hs (um (embU hF h)) = hs (um h) + 1 := hs_emb (um h)
    have h3 : 1 ≤ hs (um h) := one_le_hs' hn h
    rw [h2] at h1
    refine h1.trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hCT0
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) L
  have hXc : Continuous fun h : UJ ε' => ap T (π (emb e (um h)) η) := hFc.comp (continuous_embU hF)
  have hrp : ∀ h : UJ ε', hs (um h) ^ (-(a + L)) * hs (um h) ^ L = hs (um h) ^ (-a) := fun h => by
    have hpos : 0 < hs (um h) := lt_of_lt_of_le one_pos (one_le_hs' hn h)
    rw [← Real.rpow_natCast, ← Real.rpow_add hpos]
    congr 1; ring
  have bound : ∀ b : H, ∀ h : UJ ε', ‖c h * ⟪b, ap T (π (emb e (um h)) η)⟫_ℂ‖ ≤ K₀ * ‖b‖ * hs (um h) ^ (-a) := by
    intro b h
    rw [norm_mul]
    calc _ ≤ (C' * hs (um h) ^ (-(a + L))) * (‖b‖ * (CT * 2 ^ L * hs (um h) ^ L)) :=
          mul_le_mul (hcb' h) ((norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hX h) (norm_nonneg _)))
            (norm_nonneg _) (mul_nonneg hC'0 (Real.rpow_nonneg (hs_nonneg' _) _))
      _ = K₀ * ‖b‖ * (hs (um h) ^ (-(a + L)) * hs (um h) ^ L) := by rw [hK₀]; ring
      _ = _ := by rw [hrp]
  have integ : ∀ b : H, Integrable (fun h : UJ ε' => c h * ⟪b, ap T (π (emb e (um h)) η)⟫_ℂ) ν := fun b =>
    (hIntR n ε' ν hν hn _ (K₀ * ‖b‖) a (hc.mul (continuous_const.inner hXc)) le_rfl (bound b)).1

  have hw : Integrable (fun h : UJ ε' => hs (um h) ^ (-a)) ν := by
    have hcw : Continuous fun h : UJ ε' => ((hs (um h) ^ (-a) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_hs_um.rpow_const fun h =>
        Or.inl (lt_of_lt_of_le one_pos (one_le_hs' hn h)).ne')
    have := (hIntR n ε' ν hν hn _ 1 a hcw le_rfl fun h => by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (hs_nonneg' _) _), one_mul]).1
    simpa using this.re
  refine ⟨integ b, ?_⟩

  set Λ : H → ℂ := fun b => ∫ h : UJ ε', c h * ⟪b, ap T (π (emb e (um h)) η)⟫_ℂ ∂ν with hΛ
  obtain ⟨T', hT'⟩ := span_adj hS L T hT
  have hS0 : ∀ b ∈ S, Λ b = 0 := by
    intro b hb
    have e1 : ∀ h : UJ ε', c h * ⟪b, ap T (π (emb e (um h)) η)⟫_ℂ =
        c h * ⟪(T' ⟨b, hb⟩ : H), π (emb e (um h)) η⟫_ℂ := fun h => by
      have hm : π (emb e (um h)) η ∈ S := hS.stab _ (embU hF h).2 _ η.2
      rw [ap_of_mem _ hm, hT' ⟨_, hm⟩ ⟨b, hb⟩]
    simp only [hΛ, e1]
    exact hzero _ _

  have hlip : ∀ b b' : H, ‖Λ b - Λ b'‖ ≤ (K₀ * ∫ h, hs (um h) ^ (-a) ∂ν) * ‖b - b'‖ := by
    intro b b'
    have e1 : Λ b - Λ b' = ∫ h : UJ ε', c h * ⟪b - b', ap T (π (emb e (um h)) η)⟫_ℂ ∂ν := by
      simp only [hΛ]
      rw [← integral_sub (integ b) (integ b')]
      refine integral_congr_ae (.of_forall fun h => ?_)
      simp only [inner_sub_left, mul_sub]
    rw [e1]
    refine (norm_integral_le_of_norm_le (hw.const_mul (K₀ * ‖b - b'‖)) (.of_forall fun h => bound _ h)).trans
      (le_of_eq ?_)
    rw [integral_const_mul]; ring
  have hcont : Continuous Λ := by
    refine LipschitzWith.continuous (K := Real.toNNReal (K₀ * ∫ h, hs (um h) ^ (-a) ∂ν))
      (LipschitzWith.of_dist_le_mul fun b b' => ?_)
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (mul_nonneg hK₀0 (integral_nonneg fun h =>
      Real.rpow_nonneg (hs_nonneg' _) _))]
    exact hlip b b'
  have hcl : IsClosed {b : H | Λ b = 0} := isClosed_eq hcont continuous_const
  have hall : closure (S : Set H) ⊆ {b : H | Λ b = 0} := closure_minimal (fun b hb => hS0 b hb) hcl
  rw [hD.closure_eq] at hall
  exact hall (Set.mem_univ b)

end ZeroSec

end PositivityTheory.RgHe.SM
end
end

section
noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe.SM

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition Formalism.FourierDecayAlt.P.CapelliAbstractCharacter CompanionTheory.D.DSIC

theorem irr : Irr := by
  intro m ε K _ _ σ hU hI u w hu hw
  by_contra hcon
  push_neg at hcon
  have hJ : PI.UpqRep.Jm ε * PI.UpqRep.Jm ε = 1 := by
    unfold PI.UpqRep.Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hlift : ∀ g ∈ UJset ε, ∃ h : UJ ε, um h = g := by
    intro g hg
    have hg' : gᴴ * PI.UpqRep.Jm ε * g = PI.UpqRep.Jm ε := hg
    have h2 : PI.UpqRep.Jm ε * gᴴ * PI.UpqRep.Jm ε * g = 1 := by
      rw [Matrix.mul_assoc (PI.UpqRep.Jm ε * gᴴ), Matrix.mul_assoc (PI.UpqRep.Jm ε),
        ← Matrix.mul_assoc gᴴ, hg', hJ]
    have h1 : g * (PI.UpqRep.Jm ε * gᴴ * PI.UpqRep.Jm ε) = 1 := mul_eq_one_comm.mp h2
    exact ⟨⟨⟨g, _, h1, h2⟩, hg⟩, rfl⟩
  have hmul : ∀ g ∈ UJset ε, ∀ h ∈ UJset ε, g * h ∈ UJset ε := by
    intro g hg h hh
    have hg' : gᴴ * PI.UpqRep.Jm ε * g = PI.UpqRep.Jm ε := hg
    have hh' : hᴴ * PI.UpqRep.Jm ε * h = PI.UpqRep.Jm ε := hh
    show (g * h)ᴴ * PI.UpqRep.Jm ε * (g * h) = PI.UpqRep.Jm ε
    rw [Matrix.conjTranspose_mul]
    calc hᴴ * gᴴ * PI.UpqRep.Jm ε * (g * h) = hᴴ * (gᴴ * PI.UpqRep.Jm ε * g) * h := by
          simp only [Matrix.mul_assoc]
      _ = PI.UpqRep.Jm ε := by rw [hg', hh']
  have hone : (1 : Matrix (Fin m) (Fin m) ℂ) ∈ UJset ε := by
    show (1 : Matrix (Fin m) (Fin m) ℂ)ᴴ * PI.UpqRep.Jm ε * 1 = PI.UpqRep.Jm ε
    simp
  let Sp : Submodule ℂ K := Submodule.span ℂ {x | ∃ g ∈ UJset ε, x = σ g u}
  have hSpinv : ∀ g ∈ UJset ε, ∀ x ∈ Sp, σ g x ∈ Sp := by
    intro g hg x hx
    refine Submodule.span_induction (p := fun x _ => σ g x ∈ Sp) ?_ ?_ ?_ ?_ hx
    · rintro y ⟨h, hh, rfl⟩
      apply Submodule.subset_span
      refine ⟨g * h, hmul g hg h hh, ?_⟩
      rw [hU.1.2 g hg h hh]
      rfl
    · simp
    · intro a b _ _ ha hb
      rw [map_add]
      exact Sp.add_mem ha hb
    · intro c a _ ha
      rw [map_smul]
      exact Sp.smul_mem c ha
  have hMinv : ∀ g ∈ UJset ε, ∀ v ∈ Sp.topologicalClosure, σ g v ∈ Sp.topologicalClosure := by
    intro g hg v hv
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hv ⊢
    exact map_mem_closure (σ g).continuous hv (fun x hx => hSpinv g hg x hx)
  have huM : u ∈ Sp.topologicalClosure := by
    apply Submodule.le_topologicalClosure
    apply Submodule.subset_span
    refine ⟨1, hone, ?_⟩
    rw [hU.1.1]
    rfl
  have hker : Sp.topologicalClosure ≤ LinearMap.ker (innerSL ℂ w : K →ₗ[ℂ] ℂ) := by
    apply Submodule.topologicalClosure_minimal
    · rw [Submodule.span_le]
      rintro x ⟨g, hg, rfl⟩
      obtain ⟨h, rfl⟩ := hlift g hg
      show innerSL ℂ w (σ (um h) u) = 0
      rw [innerSL_apply_apply]
      exact hcon h
    · exact ContinuousLinearMap.isClosed_ker _
  rcases hI _ (Submodule.isClosed_topologicalClosure _) hMinv with h0 | htop
  · rw [h0] at huM
    exact hu ((Submodule.mem_bot ℂ).mp huM)
  · have hwM : w ∈ Sp.topologicalClosure := by
      rw [htop]
      exact Submodule.mem_top
    have hw0 := hker hwM
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply, inner_self_eq_zero] at hw0
    exact hw hw0

theorem emb_row {n : ℕ} {e : Fin n ⊕ Unit ≃ Fin (n + 1)} (a : Matrix (Fin n) (Fin n) ℂ) (d : Fin (n + 1)) :
    emb e a (zi e) d = if d = zi e then 1 else 0 := by
  unfold emb zi
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases h : e.symm d with i | u
  · have hne : d ≠ e (Sum.inr ()) := by
      intro hd
      rw [hd, Equiv.symm_apply_apply] at h
      cases h
    simp [hne]
  · cases u
    have heq : d = e (Sum.inr ()) := by rw [← h, Equiv.apply_symm_apply]
    simp [heq]

theorem emb_ll {n : ℕ} {e : Fin n ⊕ Unit ≃ Fin (n + 1)} (a : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    emb e a (e (Sum.inl i)) (e (Sum.inl j)) = a i j := by
  simp [emb]

theorem emb_rl {n : ℕ} {e : Fin n ⊕ Unit ≃ Fin (n + 1)} (a : Matrix (Fin n) (Fin n) ℂ) (u : Unit) (j : Fin n) :
    emb e a (e (Sum.inr u)) (e (Sum.inl j)) = 0 := by
  simp [emb]

theorem phiEq : PhiEq := by
  intro n ε ε' e H H' _ _ _ _ π σ S E P hF hS hU hP η hη
  have hJJ : Jm ε' * Jm ε' = 1 := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hlift : ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * Jm ε' * g = Jm ε' → ∃ h : UJ ε', um h = g := by
    intro g hg
    have h2 : Jm ε' * gᴴ * Jm ε' * g = 1 := by
      rw [Matrix.mul_assoc (Jm ε' * gᴴ), Matrix.mul_assoc (Jm ε'), ← Matrix.mul_assoc gᴴ, hg, hJJ]
    have h1 : g * (Jm ε' * gᴴ * Jm ε') = 1 := mul_eq_one_comm.mp h2
    exact ⟨⟨⟨g, _, h1, h2⟩, hg⟩, rfl⟩
  have hembJ : ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * Jm ε' * g = Jm ε' →
      (emb e g)ᴴ * Jm ε * emb e g = Jm ε := by
    intro g hg
    rw [jm_emb hF, emb_ct, ← emb_mul, ← emb_mul, hg]
  have hsm : ∀ x ∈ S, P x ∈ PI.PhMeasCore.smoothVecs (Jm ε') σ := by
    intro x hx
    show PI.PhMeasCore.SmoothOnH _ _
    intro g₀ hg₀
    have hx' : PI.PhMeasCore.SmoothOnH (Jm ε) (fun g => π g x) := (hS.mem x).mp hx
    obtain ⟨U, F, hUo, hg₀U, hFc, hFeq⟩ := hx' (emb e g₀) (hembJ g₀ hg₀)
    letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedAddCommGroup
    letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedSpace
    letI : NormedAddCommGroup (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := Matrix.normedAddCommGroup
    letI : NormedSpace ℝ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := Matrix.normedSpace
    let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
      { toFun := fun g => emb e g - emb e 0
        map_add' := by
          intro a b
          ext i j
          simp only [emb, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.add_apply]
          rcases e.symm i with i' | i' <;> rcases e.symm j with j' | j' <;> simp
        map_smul' := by
          intro c a
          ext i j
          simp only [emb, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
            RingHom.id_apply]
          rcases e.symm i with i' | i' <;> rcases e.symm j with j' | j' <;> simp }
    have hembd : ContDiff ℝ (⊤ : ℕ∞) (emb e) := by
      have hfun : emb e = fun g => L g + emb e 0 := by
        funext g
        show emb e g = emb e g - emb e 0 + emb e 0
        abel
      rw [hfun]
      exact (LinearMap.toContinuousLinearMap L).contDiff.add contDiff_const
    refine ⟨emb e ⁻¹' U, fun g => P (F (emb e g)), hUo.preimage hembd.continuous, hg₀U, ?_, ?_⟩
    · exact (P.restrictScalars ℝ).contDiff.comp_contDiffOn (hFc.comp hembd.contDiffOn (fun g hg => hg))
    · intro g hgU hgH
      have hgH' : gᴴ * Jm ε' * g = Jm ε' := hgH
      have h1 := hFeq (emb e g) hgU (hembJ g hgH')
      obtain ⟨h, rfl⟩ := hlift g hgH'
      show σ (um h) (P x) = P (F (emb e (um h)))
      rw [← h1, ← hP.2 h x]
  refine ⟨fun l => ?_, fun h => ?_⟩
  · show P (ap (E (e (Sum.inl l)) (zi e)) η) ∈ _
    unfold ap
    rw [dif_pos hη]
    exact hsm _ (Subtype.coe_prop _)
  · have hgU : emb e (um h) ∈ UJset ε := (embU hF h).2
    have hgiU : emb e (um h⁻¹) ∈ UJset ε := (embU hF h⁻¹).2
    have hu1 : um h⁻¹ * um h = 1 := by simp [PositivityTheory.UnitaryDecomposition.um]
    have hu2 : um h * um h⁻¹ = 1 := by simp [PositivityTheory.UnitaryDecomposition.um]
    have hgg : emb e (um h⁻¹) * emb e (um h) = 1 := by rw [← emb_mul, hu1, emb_one]
    have hgg' : emb e (um h) * emb e (um h⁻¹) = 1 := by rw [← emb_mul, hu2, emb_one]
    have hinv : (emb e (um h⁻¹))⁻¹ = emb e (um h) := Matrix.inv_eq_right_inv hgg
    have hπη : π (emb e (um h)) η ∈ S := hS.stab _ hgU η hη
    have hcomp1 : ∀ y, π (emb e (um h⁻¹)) (π (emb e (um h)) y) = y := by
      intro y
      rw [← ContinuousLinearMap.comp_apply, ← hU.1.2 _ hgiU _ hgU, hgg, hU.1.1]
      rfl
    have hcomp2 : ∀ y, π (emb e (um h)) (π (emb e (um h⁻¹)) y) = y := by
      intro y
      rw [← ContinuousLinearMap.comp_apply, ← hU.1.2 _ hgU _ hgiU, hgg', hU.1.1]
      rfl
    funext c0
    show P (ap (E (e (Sum.inl c0)) (zi e)) (π (emb e (um h)) η)) =
      ∑ d, (um h)⁻¹ d c0 • σ (um h) (P (ap (E (e (Sum.inl d)) (zi e)) η))
    simp only [ap, dif_pos hη, dif_pos hπη]
    have hc := hS.conj _ hgiU (e (Sum.inl c0)) (zi e) ⟨π (emb e (um h)) η, hπη⟩ ⟨η, hη⟩ (hcomp1 η).symm
    rw [hinv] at hc
    simp only [emb_row, mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, ite_true] at hc
    have hc2 := congrArg (fun y => P (π (emb e (um h)) y)) hc
    simp only [hcomp2, map_sum, map_smul] at hc2
    rw [hc2, ← e.sum_comp, Fintype.sum_sum_type]
    simp only [emb_rl, zero_smul, Finset.sum_const_zero, add_zero, emb_ll, um_inv]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [hP.2 h]

end PositivityTheory.RgHe.SM
end
end

section
noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe.SM

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition Formalism.FourierDecayAlt.P.CapelliAbstractCharacter CompanionTheory.D.DSIC

theorem gap_mono {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {h h' : ℝ} (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (hh : h' ≤ h) :
    Formalism.QuantumDeterminants.GapAtLeast ε lam h' := fun a b hab => hh.trans (hg a b hab)

set_option maxHeartbeats 1600000 in
theorem stepM_of (hKey : KeyId) (hZ : Zero) (hPhi : PhiEq) (hIrr : Irr) :
    Models → OfInt → Seed → DecEx2 → StepM := by
  intro hMod hOf _ hDec n ε lam ε' mu e hG j hG' hwall hOcc
  refine (hMod n ε lam ε' (mu - Pi.single j 1) e hG').1 ?_
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by have := hG.two; omega⟩
  have hN1 : 1 ≤ N + 1 := by omega
  have hc1 : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have gG : Formalism.QuantumDeterminants.GapAtLeast ε lam (200 * ((N + 2 : ℕ) : ℝ) ^ 3) := by
    have h := hG.gap
    refine gap_mono h (le_of_eq ?_)
    push_cast; ring
  have gH : Formalism.QuantumDeterminants.GapAtLeast ε' mu (200 * ((N + 1 : ℕ) : ℝ) ^ 3) :=
    gap_mono hG.gap' (by have : ((N + 1 : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) + 1 := by linarith
                         have := pow_le_pow_left₀ hc1 this 3; linarith)
  obtain ⟨H, i1, i2, π, hπ⟩ := exists_ds ε lam (by omega) hG.hc gG
  obtain ⟨H', i3, i4, σ, hσ⟩ := exists_ds ε' mu hN1 hG.hc' gH
  haveI : CompleteSpace H := hπ.1
  haveI : CompleteSpace H' := hσ.1
  obtain ⟨j0, hj0, hj0m⟩ := hOcc H H' π σ hπ hσ
  obtain ⟨P, hP, hP0⟩ := exists_P hG.fits hπ hσ hj0 hj0m
  obtain ⟨S, E, hS⟩ := hSmMod (N + 2) ε H π hπ.2.2.1
  obtain ⟨S', E', hS'⟩ := hSmMod (N + 1) ε' H' σ hσ.2.2.1
  obtain ⟨X, hXS, hXκ⟩ := hDec (N + 1) ε' mu H' σ (signs hG).1 (signs hG).2 hG.hc' hσ gH
  have hj : j ∈ X.S := (hXS j).2 hG'.hc'
  have hσ' := (X.ds j hj).2
  obtain ⟨η₀, hη₀, hne⟩ := WordSpanNonVanishing.nonvan hKey hG hπ hσ hS hS' hP hP0 X hXκ j hj hwall
  obtain ⟨R, hR, hRe⟩ := WordSpaces.pj_words hG hπ hσ hS hS' hP X hXκ j hj
  have hUπ := hπ.2.2.1
  have hUσ := hσ.2.2.1
  have hden : Dense (S : Set H) :=
    dense_sm (by omega) hG.hc hπ (gap_mono gG (by have : (0 : ℝ) ≤ ((N + 2 : ℕ) : ℝ) ^ 3 := by positivity
                                                  linarith)) hS

  have hφ₀ := (hPhi (N + 1) ε ε' e H H' π σ S E P hG.fits hS hUπ hP η₀ hη₀).1
  have hx₀ := X.p_sm j hj _ hφ₀
  obtain ⟨l, hl⟩ : ∃ l, X.p j (phi E e P η₀) l ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have hy := smT_single (hx₀ l) l
  have hform := X.form j hj _ hφ₀ _ hy
  rw [formT_single] at hform
  have hprod : X.c j * ⟪X.pr j (Pi.single l (X.p j (phi E e P η₀) l)), X.pr j (phi E e P η₀)⟫_ℂ ≠ 0 := by
    rw [← hform]
    refine mul_ne_zero (by split_ifs <;> norm_num) ?_
    rw [inner_self_ne_zero]; exact hl
  have hcj : X.c j ≠ 0 := left_ne_zero_of_mul hprod
  have hpr2 := right_ne_zero_of_mul hprod
  have hpry : X.pr j (Pi.single l (X.p j (phi E e P η₀) l)) ≠ 0 := fun h0 => hpr2 (by rw [h0, inner_zero_left])
  have hprφ : X.pr j (phi E e P η₀) ≠ 0 := fun h0 => hpr2 (by rw [h0, inner_zero_right])
  obtain ⟨w', hw', hw'1⟩ := exists_low hσ'
  have hw'0 : w' ≠ 0 := fun h0 => by rw [h0, norm_zero] at hw'1; exact zero_ne_one hw'1
  obtain ⟨h₁, hh₁⟩ := hIrr (N + 1) ε' _ (X.πs j) hσ'.2.2.1 hσ'.2.2.2.1 _ w' hprφ hw'0
  obtain ⟨h₂, hh₂⟩ := hIrr (N + 1) ε' _ (X.πs j) hσ'.2.2.1 hσ'.2.2.2.1 _ w' hpry hw'0
  set y := (Pi.single l (X.p j (phi E e P η₀) l) : Fin (N + 1) → H') with hyd
  have hmem : ∀ h : UJ ε', emb e (um h) ∈ UJset ε := fun h => Formalism.MainNotions.BridgeCSchur.umat_mem (embU hG.fits h)
  set η₁ := π (emb e (um h₁)) η₀ with hη₁d
  have hη₁ : η₁ ∈ S := hS.stab _ (hmem h₁) η₀ hη₀
  have hφ₁e := (hPhi (N + 1) ε ε' e H H' π σ S E P hG.fits hS hUπ hP η₀ hη₀).2 h₁
  have hφ₁ := (hPhi (N + 1) ε ε' e H H' π σ S E P hG.fits hS hUπ hP η₁ hη₁).1
  have hprφ₁ : X.pr j (phi E e P η₁) = X.πs j (um h₁) (X.pr j (phi E e P η₀)) := by
    rw [hφ₁e]; exact X.pr_act j hj h₁ _ hφ₀
  set y₂ := actT σ (um h₂) y with hy₂d
  have hy₂ : y₂ ∈ SmT ε' σ := smT_act hUσ h₂ hy
  have hpry₂ : X.pr j y₂ = X.πs j (um h₂) (X.pr j y) := X.pr_act j hj h₂ _ hy
  have hA : ⟪X.pr j y₂, w'⟫_ℂ ≠ 0 := by
    rw [hpry₂, ← inner_conj_symm]; exact (map_ne_zero _).2 hh₂
  have hB : ⟪w', X.pr j (phi E e P η₁)⟫_ℂ ≠ 0 := by rw [hprφ₁]; exact hh₁
  obtain ⟨κ', hκ', hsch⟩ := schur_haar hσ' (muG ε')
  obtain ⟨hcont, C, hCb⟩ := decay_low hN1 hG'.hc' hσ' hG'.gap' hw' hw'1
  by_contra hnot
  have hall : ∀ a b : H, ∫ h : UJ ε', conj ⟪w', X.πs j (um h) w'⟫_ℂ * ⟪b, π (emb e (um h)) a⟫_ℂ ∂(muG ε') = 0 := by
    intro a b
    by_contra hab
    obtain ⟨j1, hj1, hj1m⟩ := hOf (N + 1) ε lam ε' (mu - Pi.single j 1) e hG' H (X.Hs j) π (X.πs j) (muG ε') inferInstance
      hπ hσ' w' hw' hw'1 a b hab
    exact hnot ⟨H, X.Hs j, inferInstance, inferInstance, inferInstance, inferInstance, π, X.πs j, hπ, hσ', j1, hj1, hj1m⟩
  have hZl := fun l' => hZ (N + 1) ε ε' e H π S E hG.fits hN1 hS hUπ hden (muG ε') inferInstance
    (fun h : UJ ε' => conj ⟪w', X.πs j (um h) w'⟫_ℂ) (N + 1) C hcont hCb hall (R l') (hR l') ⟨η₁, hη₁⟩
    (ContinuousLinearMap.adjoint P (y₂ l'))
  have hpt : ∀ h : UJ ε', conj ⟪w', X.πs j (um h) w'⟫_ℂ * formT ε' y₂ (X.p j (phi E e P (π (emb e (um h)) η₁))) =
      ∑ l', (if ε' l' then 1 else -1) * (conj ⟪w', X.πs j (um h) w'⟫_ℂ *
        ⟪ContinuousLinearMap.adjoint P (y₂ l'), ap (R l') (π (emb e (um h)) η₁)⟫_ℂ) := by
    intro h
    have e2 : ∀ l', X.p j (phi E e P (π (emb e (um h)) η₁)) l' = P (ap (R l') (π (emb e (um h)) η₁)) :=
      hRe _ (hS.stab _ (hmem h) η₁ hη₁)
    simp only [formT, e2, ← ContinuousLinearMap.adjoint_inner_left, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l' _ => by ring
  have hpt2 : ∀ h : UJ ε', conj ⟪w', X.πs j (um h) w'⟫_ℂ * formT ε' y₂ (X.p j (phi E e P (π (emb e (um h)) η₁))) =
      X.c j * (⟪X.pr j y₂, X.πs j (um h) (X.pr j (phi E e P η₁))⟫_ℂ * conj ⟪w', X.πs j (um h) w'⟫_ℂ) := by
    intro h
    have e1 := (hPhi (N + 1) ε ε' e H H' π σ S E P hG.fits hS hUπ hP η₁ hη₁).2 h
    rw [e1, X.form j hj _ (smT_act hUσ h hφ₁) _ hy₂, X.pr_act j hj h _ hφ₁]
    ring
  have hI0 : ∫ h : UJ ε', conj ⟪w', X.πs j (um h) w'⟫_ℂ * formT ε' y₂ (X.p j (phi E e P (π (emb e (um h)) η₁))) ∂(muG ε') = 0 := by
    rw [integral_congr_ae (.of_forall hpt), integral_finsetSum _ fun l' _ => (hZl l').1.const_mul _]
    exact Finset.sum_eq_zero fun l' _ => by rw [integral_const_mul, (hZl l').2, mul_zero]
  rw [integral_congr_ae (.of_forall hpt2), integral_const_mul, (hsch _ _ _ _).2] at hI0
  have hκ0 : (κ' : ℂ) ≠ 0 := by exact_mod_cast hκ'.ne'
  exact mul_ne_zero hcj (mul_ne_zero hκ0 (mul_ne_zero hB hA)) hI0

end PositivityTheory.RgHe.SM

namespace PositivityTheory.RgHe.SM

theorem model_walk_of_inputs : Models → OfInt → Seed → DecEx2 → StepM := stepM_of keyId zero_proof phiEq irr

end PositivityTheory.RgHe.SM
end
end

section
namespace PositivityTheory.RgHe.SM

theorem stepM : PositivityTheory.RgHe.Models → PositivityTheory.RgHe.OfInt → PositivityTheory.RgHe.Seed → PositivityTheory.RgHe.DecEx2 → PositivityTheory.RgHe.StepM := model_walk_of_inputs

end PositivityTheory.RgHe.SM
end
