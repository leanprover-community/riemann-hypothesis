import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXOmVSt
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MultiplicityGExists

section
noncomputable section

namespace Formalism.L2.SG.Pf.NcX.OmVSt

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory NumberField IsDedekindDomain

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem n_sub_a : X.B.I.n - (D.R.rS + 1 + D.R.rS) = D.R.k := by
  have h1 := X.n_eq
  have h2 := D.R.rS_two
  unfold Ranks.r at h1
  omega

theorem a_le_n : D.R.rS + 1 + D.R.rS ≤ X.B.I.n := by
  have h1 := X.n_eq
  have h2 := D.R.rS_two
  unfold Ranks.r at h1
  omega

theorem fac_nonneg (v : PlX X) (j : ℕ) :
    0 ≤ 1 - (etaV (E := X.B.I.E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)) := by
  have hq : (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have h1 : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ hq (by omega)
  have h0 : 0 ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)) := by positivity
  have he : (etaV (E := X.B.I.E) v : ℝ) ^ j = 1 ∨ (etaV (E := X.B.I.E) v : ℝ) ^ j = -1 := by
    unfold etaV
    split_ifs
    · left; simp
    · push_cast; exact neg_one_pow_eq_or ℝ j
  rcases he with h | h <;> rw [h] <;> linarith

theorem val_nonneg (v : PlX X) (x : ℝ) (s : Finset ℕ) :
    0 ≤ absV v (dV v) ^ x * ∏ j ∈ s,
      (1 - (etaV (E := X.B.I.E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ))) := by
  refine mul_nonneg (Real.rpow_nonneg ?_ _) (Finset.prod_nonneg fun j _ => fac_nonneg X v j)
  unfold absV
  split_ifs <;> positivity

theorem prod_eq (v : PlX X) (s : Finset ℕ) :
    ∏ j ∈ s, (1 - (etaV (E := X.B.I.E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ))) =
      ∏ i ∈ s, (1 - ((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ i / ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ i) := by
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [zpow_neg, zpow_natCast, div_eq_mul_inv]

theorem exp_eq :
    (X.B.I.n : ℝ) * ((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) - ((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) ^ 2 / 2 =
      (X.B.I.n : ℝ) * (2 * D.R.rS + 1) - ((2 * (D.R.rS : ℝ) + 1) ^ 2) / 2 := by
  push_cast; ring

theorem omV_of (hStd : OmVStd X ψ) (hLat : OmVLat X) (hSD : OmVSD X) (hUn : OmVUnram X) (hPrim : OmVPrim X u')
    (hGram : OmVGram X u') (hDet : OmVDet X u') (hScale : OmVScale X u' ψ) (hBad : OmVBadT X u' ψ)
    (hLocU : OmVLocU X ψ) : Formalism.L2.SG.Pf.NcVal.OmV X u' ψ := by
  intro hψ hψ' v
  show (omAt X.B.I.cm.sig X.B.I.J ψ v (localGramMatrixFrame X u' v)
      {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))}).toReal = _
  rw [hScale hψ hψ' v]
  by_cases hT : ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal
  · rw [hBad hψ hψ' v hT (hSD v) (hUn v) (hPrim v), ENNReal.toReal_ofReal (val_nonneg X v _ _), exp_eq X, prod_eq X v]
    unfold aP
    rw [if_pos hT, n_sub_a X]
  · have h := hLocU v _ (yTup X u' v) (hStd hψ hψ') hLat (hSD v) (hUn v) (a_le_n X) (hPrim v)
      (by rw [hGram v]; exact hDet v hT)
    rw [hGram v] at h
    rw [h, ENNReal.toReal_ofReal (val_nonneg X v _ _), exp_eq X, prod_eq X v]
    unfold aP
    rw [if_neg hT, n_sub_a X]

end Formalism.L2.SG.Pf.NcX.OmVSt
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.NcX.OmVSt

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

theorem unramAt_of_cm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (v : HeightOneSpectrum (𝓞 F)) : UnramAt (E := E) v := by
  intro P hP hP0 _
  classical
  haveI : Algebra.IsQuadraticExtension F E := ⟨hc.deg2⟩
  let c : Gal(E/F) := AlgEquiv.ofRingEquiv (f := starRingAut) (fun r => (hc.fixed (algebraMap F E r)).2 ⟨r, rfl⟩)
  haveI : P.LiesOver (P.under (𝓞 F)) := ⟨rfl⟩
  have hp0 : P.under (𝓞 F) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 F) hP0
  have hcard : Nat.card (P.inertia Gal(E/F)) = P.ramificationIdx (𝓞 F) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(E/F)) (P.under (𝓞 F)) P,
      Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 F)) P Gal(E/F)]
  by_contra hne
  have hG : Nat.card Gal(E/F) = 2 := by
    first
      | (rw [IsGalois.card_aut_eq_finrank]; exact hc.deg2)
      | (rw [Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]; exact hc.deg2)
  haveI : Fact (Nat.card Gal(E/F)).Prime := ⟨by rw [hG]; exact Nat.prime_two⟩
  have htop : P.inertia Gal(E/F) = ⊤ := by
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (P.inertia Gal(E/F)) with h | h
    · exfalso
      apply hne
      rw [← hcard, h]
      simp
    · exact h
  have hcI : c ∈ P.inertia Gal(E/F) := htop ▸ Subgroup.mem_top c
  obtain ⟨θ, t, ht, hθ⟩ := hc.cmUnram.2.2 P (hP.isMaximal hP0)
  apply hθ
  have h1 := hcI θ
  have e : c • θ = t := by
    apply RingOfIntegers.coe_injective
    rw [ht]
    rfl
  rw [e] at h1
  have : θ - t = -(t - θ) := by ring
  rw [this]
  exact P.neg_mem h1

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omega_standard_holds : OmVStd X ψ := by
  intro h1 h2
  refine ⟨?_, ?_, h1, h2⟩
  · unfold IsCMExt
    refine ⟨X.B.I.cm.totReal, X.B.I.cm.cmUnram.1, X.B.I.cm.deg2, ?_⟩
    exact fun τ x => X.B.I.cm.cmUnram.2.1 τ x
  · unfold IsHermND
    have hH := X.B.I.J_herm
    unfold Formalism.UG.IsHerm at hH
    refine ⟨fun i j => ?_, X.B.I.J_det⟩
    have h3 := congrFun (congrFun hH i) j
    exact h3

theorem omega_lattice_holds : OmVLat X := ⟨X.B.I.L, ⟨X.B.I.L_fg, X.B.I.L_span⟩, rfl⟩

theorem omega_unramified_holds : OmVUnram X := fun v => unramAt_of_cm X.B.I.cm v

end Formalism.L2.SG.Pf.NcX.OmVSt
end
end
