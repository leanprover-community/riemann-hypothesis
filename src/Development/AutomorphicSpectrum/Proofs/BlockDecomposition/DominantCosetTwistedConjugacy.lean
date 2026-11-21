import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmFieldStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriAndMaximalCompactCriteria
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightExponentStrictlyAntitone
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagTMemIwGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriOrbitalSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactElementEigenvaluesUnits

section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.DiagRigid

theorem diag_rigid : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) (y : Fin n → ℤ), Function.Injective y → ∀ (d d' : Fin n → Lˣ), (∀ i, ordL (d i : L) = y i) → (∀ i, ordL (d' i : L) = y i) → ∀ h : GL (Fin n) L, h⁻¹ * GlobalTheory.SmGL.diagT L (Fin n) d * h = GlobalTheory.SmGL.diagT L (Fin n) d' → d = d' ∧ ∃ s : Fin n → Lˣ, h = GlobalTheory.SmGL.diagT L (Fin n) s := by
  intro L _ _ n y hy d d' hd hd' h hh
  have key : GlobalTheory.SmGL.diagT L (Fin n) d * h = h * GlobalTheory.SmGL.diagT L (Fin n) d' := by
    rw [← hh]; simp only [mul_assoc, mul_inv_cancel_left]
  have key' : (Matrix.diagonal fun i => (d i : L)) * (h : Matrix (Fin n) (Fin n) L)
      = (h : Matrix (Fin n) (Fin n) L) * Matrix.diagonal fun i => (d' i : L) := by
    have := congrArg (fun g : GL (Fin n) L => (g : Matrix (Fin n) (Fin n) L)) key
    simpa only [Units.val_mul, GlobalTheory.SmGL.val_diagT] using this
  have ent : ∀ i j, (d i : L) * (h : Matrix (Fin n) (Fin n) L) i j
      = (h : Matrix (Fin n) (Fin n) L) i j * (d' j : L) := by
    intro i j
    have := congrFun (congrFun key' i) j
    rwa [Matrix.diagonal_mul, Matrix.mul_diagonal] at this
  have off : ∀ i j, i ≠ j → (h : Matrix (Fin n) (Fin n) L) i j = 0 := by
    intro i j hij
    by_contra hne
    have e : (d i : L) = (d' j : L) := by
      have := ent i j
      rw [mul_comm] at this
      exact mul_left_cancel₀ hne this
    apply hij
    apply hy
    rw [← hd i, ← hd' j, e]
  have hdiag : (h : Matrix (Fin n) (Fin n) L)
      = Matrix.diagonal fun i => (h : Matrix (Fin n) (Fin n) L) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.diagonal_apply_ne _ hij]; exact off i j hij
  have hdet : ∏ i, (h : Matrix (Fin n) (Fin n) L) i i ≠ 0 := by
    have h1 : IsUnit (h : Matrix (Fin n) (Fin n) L).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 h.isUnit
    rw [hdiag, Matrix.det_diagonal] at h1
    simpa [Matrix.diagonal_apply_eq] using h1.ne_zero
  have hii : ∀ i, (h : Matrix (Fin n) (Fin n) L) i i ≠ 0 := fun i =>
    (Finset.prod_ne_zero_iff.1 hdet) i (Finset.mem_univ i)
  refine ⟨?_, fun i => Units.mk0 _ (hii i), ?_⟩
  · funext i
    apply Units.ext
    have := ent i i
    rw [mul_comm] at this
    exact mul_left_cancel₀ (hii i) this
  · apply Units.ext
    rw [GlobalTheory.SmGL.val_diagT]
    simpa using hdiag

end GlobalTheory.CompanionTheory.DiagRigid
end

section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CptGen

theorem cptPart_eq_inf : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (T C : Subgroup G), IsCompact (C : Set G) → (∀ t ∈ T, IsCompact (closure (Subgroup.zpowers t : Set G)) → t ∈ C) → cptPart T = T ⊓ C := by
  intro G _ _ _ _ T C hC h
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    intro x hx
    exact ⟨hx.1, h x hx.1 hx.2⟩
  · intro x hx
    apply Subgroup.subset_closure
    refine ⟨hx.1, hC.of_isClosed_subset isClosed_closure ?_⟩
    exact closure_minimal (fun y hy => (Subgroup.zpowers_le.2 hx.2) hy) hC.isClosed

end GlobalTheory.CompanionTheory.CptGen
end

section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SuppCent

theorem comm_of_conj {G : Type} [Group G] (γ p₀ q : G)
    (h : q⁻¹ * (p₀⁻¹ * γ * p₀) * q = p₀⁻¹ * γ * p₀) :
    (p₀ * q * p₀⁻¹) * γ = γ * (p₀ * q * p₀⁻¹) := by
  calc (p₀ * q * p₀⁻¹) * γ = p₀ * q * (p₀⁻¹ * γ * p₀) * p₀⁻¹ := by group
    _ = p₀ * q * (q⁻¹ * (p₀⁻¹ * γ * p₀) * q) * p₀⁻¹ := by rw [h]
    _ = γ * (p₀ * q * p₀⁻¹) := by group

theorem conj_comm {G : Type} [Group G] (γ p₀ t : G) (h : t * γ = γ * t) :
    (p₀⁻¹ * t * p₀)⁻¹ * (p₀⁻¹ * γ * p₀) * (p₀⁻¹ * t * p₀) = p₀⁻¹ * γ * p₀ := by
  calc _ = p₀⁻¹ * t⁻¹ * (γ * t) * p₀ := by group
    _ = p₀⁻¹ * t⁻¹ * (t * γ) * p₀ := by rw [h]
    _ = _ := by group

theorem isCompact_closure_zpowers_conj {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] (c t : G)
    (h : IsCompact (closure (Subgroup.zpowers t : Set G))) :
    IsCompact (closure (Subgroup.zpowers (c⁻¹ * t * c) : Set G)) := by
  have hφ : Continuous fun x : G => c⁻¹ * x * c := by fun_prop
  have hK := h.image hφ
  refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
  rintro _ ⟨k, rfl⟩
  refine ⟨t ^ k, subset_closure (Subgroup.zpow_mem_zpowers t k), ?_⟩
  have e : c⁻¹ * t * c = MulAut.conj c⁻¹ t := by simp [MulAut.conj_apply]
  have e' : ∀ x : G, c⁻¹ * x * c = MulAut.conj c⁻¹ x := fun x => by simp [MulAut.conj_apply]
  simp only [e', map_zpow]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifAt ϖ → ∀ (l : Fin (n / 2) → ℤ), Cone l → (∀ (y : Fin n → ℤ), StrictAnti y → ∀ δ : GLw n w, dcos n w (tdiag ϖ y) δ ≠ 0 → ∃ m ∈ iwGL n w, ∃ τ : GLw n w, ((∀ i j : Fin n, i ≠ j → τ.val i j = 0) ∧ ∀ i, Valued.v (τ.val i i) = 1) ∧ m⁻¹ * δ * m = tdiag ϖ y * τ) → ∀ γ : UL n w, (∃ p : UL n w, fU n w b ϖ l (p⁻¹ * γ * p) ≠ 0) → ∃ (p₀ : UL n w) (u : Fin n → (w.adicCompletion E)ˣ), (∀ i, ordL (u i : w.adicCompletion E) = wexp n l i) ∧ (p₀⁻¹ * γ * p₀).1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹ ∧ (∀ p : UL n w, fU n w b ϖ l (p⁻¹ * γ * p) ≠ 0 ↔ ∃ z ∈ twCent (MonoidHom.id (UL n w)) γ, ∃ i ∈ iwU n w b, p = z * p₀ * i) ∧ cptPart (twCent (MonoidHom.id (UL n w)) γ) = twCent (MonoidHom.id (UL n w)) γ ⊓ (iwU n w b).map (MulAut.conj p₀).toMonoidHom := by
  intro E _ _ _ hU w hw n b hb ϖ hϖ l hl hyp γ ⟨p1, hp1⟩
  obtain ⟨hW1, hW2, hWc, -⟩ := GlobalTheory.CompanionTheory.UnitaryWitt.unitary_hyperbolic_basis E hU w hw n b hb
  have hinj : Function.Injective (wexp n l) :=
    (GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev n l hl).1.injective
  have huc := GlobalTheory.CompanionTheory.UnitaryContraction.main E hU w hw n b hb ϖ hϖ l hl hyp
  obtain ⟨m, hm, u, hu, hmu⟩ := huc _ hp1
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : UL n w, p₀ = p1 * m := ⟨_, rfl⟩
  have hγ0 : (p₀⁻¹ * γ * p₀).1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹ := by
    rw [← hmu]
    congr 1
    rw [hp₀]
    group

  have key : ∀ (q : UL n w) (u' : Fin n → (w.adicCompletion E)ˣ),
      (∀ i, ordL (u' i : w.adicCompletion E) = wexp n l i) →
      (q⁻¹ * (p₀⁻¹ * γ * p₀) * q).1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u' * b⁻¹ →
      u = u' ∧ ∃ s : Fin n → (w.adicCompletion E)ˣ,
        q.1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s * b⁻¹ := by
    intro q u' hu' e
    have e' : q.1⁻¹ * (b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹) * q.1 =
        b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u' * b⁻¹ := by
      rw [← hγ0, ← e]
      rfl
    have hh : (b⁻¹ * q.1 * b)⁻¹ * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * (b⁻¹ * q.1 * b) =
        GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u' := by
      calc _ = b⁻¹ * (q.1⁻¹ * (b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹) * q.1) * b := by
            group
        _ = _ := by rw [e']; group
    obtain ⟨h1, s, hs⟩ := GlobalTheory.CompanionTheory.DiagRigid.diag_rigid (w.adicCompletion E) n (wexp n l) hinj u u'
      hu hu' _ hh
    refine ⟨h1, s, ?_⟩
    rw [← hs]
    group
  refine ⟨p₀, u, hu, hγ0, fun p => ⟨fun hp => ?_, ?_⟩, ?_⟩
  ·
    obtain ⟨m', hm', u', hu', e⟩ := huc _ hp
    have e2 : (p₀⁻¹ * p * m')⁻¹ * (p₀⁻¹ * γ * p₀) * (p₀⁻¹ * p * m') = m'⁻¹ * (p⁻¹ * γ * p) * m' := by
      group
    obtain ⟨rfl, -⟩ := key (p₀⁻¹ * p * m') u' hu' (by rw [e2]; exact e)
    have hq : (p₀⁻¹ * p * m')⁻¹ * (p₀⁻¹ * γ * p₀) * (p₀⁻¹ * p * m') = p₀⁻¹ * γ * p₀ := by
      apply Subtype.ext
      rw [e2, e, hγ0]
    refine ⟨p₀ * (p₀⁻¹ * p * m') * p₀⁻¹, comm_of_conj γ p₀ _ hq, m'⁻¹, inv_mem hm', ?_⟩
    group
  ·
    rintro ⟨z, hz, i, hi, rfl⟩
    have hz' : z * γ = γ * z := hz
    have e : (z * p₀ * i)⁻¹ * γ * (z * p₀ * i) = i⁻¹ * (p₀⁻¹ * γ * p₀) * i := by
      calc _ = i⁻¹ * p₀⁻¹ * z⁻¹ * (γ * z) * p₀ * i := by group
        _ = i⁻¹ * p₀⁻¹ * z⁻¹ * (z * γ) * p₀ * i := by rw [hz']
        _ = _ := by group
    rw [e, GlobalTheory.CompanionTheory.DiagCoset.fU_diag E hU w hw n b hb ϖ hϖ l hl _ u hu hγ0 _ (inv_mem hi) _ hi]
    exact one_ne_zero
  ·
    refine GlobalTheory.CompanionTheory.CptGen.cptPart_eq_inf (UL n w) _ _ ?_ ?_
    · rw [Subgroup.coe_map]
      refine hWc.image ?_
      change Continuous fun x : UL n w => p₀ * x * p₀⁻¹
      fun_prop
    · intro t ht hc
      have ht' : t * γ = γ * t := ht
      obtain ⟨-, s, hs⟩ := key (p₀⁻¹ * t * p₀) u hu (by rw [conj_comm γ p₀ t ht']; exact hγ0)
      have hv := GlobalTheory.CompanionTheory.DiagBd.valued_eq_one_of_isCompact_closure_zpowers E w n (UL n w)
        (p₀⁻¹ * t * p₀) b s hs (isCompact_closure_zpowers_conj p₀ t hc)
      have hmem : p₀⁻¹ * t * p₀ ∈ iwU n w b := by
        rw [hW2]
        have : b⁻¹ * (p₀⁻¹ * t * p₀).1 * b = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s := by
          rw [hs]
          group
        rw [this]
        exact GlobalTheory.CompanionTheory.DiagCoset.diagT_mem_iwGL w n s hv
      refine Subgroup.mem_map.2 ⟨_, hmem, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]

end GlobalTheory.CompanionTheory.SuppCent
end
