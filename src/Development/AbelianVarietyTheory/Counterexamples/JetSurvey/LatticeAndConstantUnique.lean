import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcWitnessExistence.DataXOfModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatIn
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRankOneCuspLatticeDataOfPrincipal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoreArithmeticGroupContainsPrincipalCongruence

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.ModelLatticeCheck

def Fits {D : D7} (T : Core D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (k : (T.U j σ).Comp) (Xx : DataX D.host.E D.R.r) : Prop :=
  Xx.toData = (T.U j σ).X k ∧ Xx.g = T.Q.l.M ∧
    Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u}

theorem comp_nonempty {D : D7} (T : Core D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) : Nonempty (T.U j σ).Comp :=
  ⟨(T.dict j σ 1).1⟩

theorem le_of_span_le {E : Type} [Field E] [NumberField E] {r : ℕ}
    (A : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hA : A ≠ 0) (L₁ L₂ : Submodule (𝓞 E) (Fin r → E))
    (h : Submodule.span (𝓞 E) {v | ∃ a ∈ A, ∃ u ∈ L₁, v = a • u} ≤
      Submodule.span (𝓞 E) {v | ∃ a ∈ A, ∃ u ∈ L₂, v = a • u}) : L₁ ≤ L₂ := by
  intro u hu
  have key : ∀ b ∈ A⁻¹, ∀ x ∈ Submodule.span (𝓞 E) {v | ∃ a ∈ A, ∃ u ∈ L₂, v = a • u}, b • x ∈ L₂ := by
    intro b hb x hx
    induction hx using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, ha, w, hw, rfl⟩ := hv
      have : b * a ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
        rw [← inv_mul_cancel₀ hA]; exact FractionalIdeal.mul_mem_mul hb ha
      obtain ⟨z, hz⟩ := (FractionalIdeal.mem_one_iff _).1 this
      rw [smul_smul, ← hz, algebraMap_smul]
      exact L₂.smul_mem z hw
    | zero => simp
    | add v w _ _ hv hw => rw [smul_add]; exact add_mem hv hw
    | smul c v _ hv => rw [smul_comm]; exact L₂.smul_mem c hv
  have h1 : (1 : E) ∈ A⁻¹ * A := by
    rw [inv_mul_cancel₀ hA]; exact FractionalIdeal.one_mem_one _
  have : ∀ c ∈ A⁻¹ * A, c • u ∈ L₂ := by
    intro c hc
    refine FractionalIdeal.mul_induction_on hc (C := fun c => c • u ∈ L₂) ?_ ?_
    · intro b hb a ha
      rw [mul_smul]
      exact key b hb _ (h (Submodule.subset_span ⟨a, ha, u, hu, rfl⟩))
    · intro x y hx hy
      rw [add_smul]; exact add_mem hx hy
  simpa using this 1 h1

theorem AA_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  intro h
  have h1 := GlobalTheory.LatticeData.absNorm_ccK_mem D
  rw [h, FractionalIdeal.mem_zero_iff] at h1
  exact D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 (by exact_mod_cast h1))



theorem holds_by_value (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ)
    (hσ : GoodEmb T.Q.c σ) (k : (T.U j σ).Comp) :
    ∃ X : DataX D.host.E D.R.r, Fits T j σ k X ∧ X.k0 = 2 * xiR D ∧ X.NA = Ideal.absNorm D.host.𝔟 ∧
      X.NC = Ideal.absNorm D.host.ccK := by
  obtain ⟨Xx, h1, h2, h3, h4, -⟩ :=
    GlobalTheory.LatticeData.exists_dataX_of_hasPrinc D T h j hj σ hσ (GlobalTheory.PrincCore.hasPrinc_core D T h j hj σ hσ) k
  refine ⟨{ Xx with
    NA := Ideal.absNorm D.host.𝔟
    NC := Ideal.absNorm D.host.ccK
    NA_pos := Nat.pos_of_ne_zero fun e => GlobalTheory.LatticeData.halfDifferent_ne_bot D (Ideal.absNorm_eq_zero_iff.1 e)
    NC_pos := Nat.pos_of_ne_zero fun e => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 e)
    NA_sub := fun x hx => ?_
    NC_sub := fun x hx => ?_ }, ⟨h1, h2, h3⟩, h4, rfl, rfl⟩
  · rw [h3] at hx
    induction hx using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, ha, u, hu, rfl⟩ := hv
      obtain ⟨z, hz⟩ := GlobalTheory.LatticeData.absNorm_mul_mem_one D ha
      rw [smul_smul, ← hz, algebraMap_smul]
      exact Xx.L'.smul_mem z hu
    | zero => simp
    | add v w _ _ hv hw => rw [smul_add]; exact add_mem hv hw
    | smul c v _ hv => rw [smul_comm]; exact Xx.L'.smul_mem c hv
  · rw [h3]
    exact Submodule.subset_span ⟨_, GlobalTheory.LatticeData.absNorm_ccK_mem D, x, hx, rfl⟩

theorem log_absNorm_le (D : D7) :
    Real.log (Ideal.absNorm D.host.𝔟 : ℕ) ≤ (fdeg D.host.E : ℝ) * Real.log (ReciprocityTheory.ChartRestriction.G.FD.rdE D.host.E) := by
  have hfr := ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.finrank_E D
  have hsq := ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.absNorm_bb_sq_le D
  have hN : 0 < Ideal.absNorm D.host.𝔟 :=
    Nat.pos_of_ne_zero fun e => GlobalTheory.LatticeData.halfDifferent_ne_bot D (Ideal.absNorm_eq_zero_iff.1 e)
  have hf0 : 0 < D.R.f := by
    have : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    omega
  have hfd : fdeg D.host.E = D.R.f := by unfold fdeg; omega
  have hd : 0 < dE D.host.E := by
    unfold dE; exact abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
  have hfR : (0 : ℝ) < D.R.f := by exact_mod_cast hf0
  have e : (fdeg D.host.E : ℝ) * Real.log (ReciprocityTheory.ChartRestriction.G.FD.rdE D.host.E) = Real.log (dE D.host.E) / 2 := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.rdE
    rw [Real.log_rpow hd, hfd, hfr]
    push_cast
    field_simp
  have hle : ((Ideal.absNorm D.host.𝔟 : ℕ) : ℝ) ^ 2 ≤ dE D.host.E := by
    have : ((Ideal.absNorm D.host.𝔟 : ℕ) : ℝ) ^ 2 ≤ ((discr D.host.E).natAbs : ℝ) := by exact_mod_cast hsq
    rw [Nat.cast_natAbs, Int.cast_abs] at this
    exact this
  have hNR : (0 : ℝ) < (Ideal.absNorm D.host.𝔟 : ℕ) := by exact_mod_cast hN
  have := Real.log_le_log (by positivity) hle
  rw [Real.log_pow] at this
  rw [e]
  push_cast at this
  linarith


theorem intersectionNumber_baseChange (D : D7) (T : Top D) (j : ℕ) : Formalism.L2.Pj.QAt.DataXOfModelSt T j := by
  intro h _ hj large₂ w hrows _ σ hσ k
  obtain ⟨X, ⟨h1, h2, h3⟩, -, hA, hC⟩ := holds_by_value D T.toCore h j hj σ hσ k
  refine ⟨X, h1, h2, ?_, ?_, h3⟩
  · rw [hA]; exact log_absNorm_le D
  · rw [hC]; exact hrows.2.2.2.1


end GlobalTheory.ModelLatticeCheck
