import Formalism.SharpRestriction.InertJacobiLevels.ExtraRec
import Formalism.LocalRingCardinality.SpanPowerMembership.TwistRecordRowDimensionZero

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.MainNotions NumberField IsDedekindDomain

variable {R : Ranks} (H : Host R)

variable (hc : Tau2 R → HCParam R) (Del : ℚ) (hDel : 0 < Del)
  (hgap : ∀ (τ : Tau2 R) (l : ℕ) (h : l + 1 < R.k - 1),
    (hc τ).v ⟨l, by omega⟩ - (hc τ).v ⟨l + 1, h⟩ = 4 * Del)
  (hlet : ∀ (τ : Tau2 R) (l : ℕ) (h : l < R.k - 2),
    (hc τ).u ⟨l + 1, by omega⟩ = (hc τ).v ⟨l, by omega⟩ - 1 / 2)
  (cdS : ∀ (n : ℕ) (_ : Fin n → Bool), NNReal) (hcdS : ∀ n ε, 0 < cdS n ε)
  (dsg : Tau2 R → ℝ) (hdsg : ∀ ρ, 0 < dsg ρ) (etaF : ℝ)

variable (hv : ℝ) (vol : @HSpace H.E _ _ H.cmStar → ℝ) (hvol : ∀ W, 0 < vol W) (K : ClsPkg)
  (T : ℕ) [hT : Fact T.Prime] (Dst : ℝ) (hD : 0 < Dst) (du : ℕ) (hdu : 0 < du) (Gam : ℝ) (hG : 1 < Gam)
  (hwin : (mem3 hc K T Dst hD du hdu Gam hG).A.Tstar ≤ (T : ℝ) ∧
    (T : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * (mem3 hc K T Dst hD du hdu Gam hG).A.Tstar)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : T ∈ H.levelPrimes) (hpde : T ≠ H.pde ∧ T ≠ H.pde')
  (pz : 𝓞 H.E) (hK : (pz : H.E) ∈ H.K) (hpz : (pz : H.E) * H.conj (pz : H.E) = (T : H.E))
  (hcong : (pz - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (lat : letI := H.cmStar; ∀ i, K.cls i → Submodule (𝓞 H.E) ((hostSpacesOfNorm H T pz hpz).X i).V)
  (hlat : letI := H.cmStar; ∀ i c, Submodule.IsLattice H.E (lat i c))
  (G : LocalGap H)
  (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)
  (tw : (@placesOf H.E _ _ H.cmStar).Pl → Bool)
  (htw : ∀ w, tw ((@placesOf H.E _ _ H.cmStar).conj w) = tw w)




















def dstFor (R : Ranks) (du : ℕ) (Ts Gam : ℝ) : ℝ := (du : ℝ) * dstarOfRanks R Ts Gam


omit hT in
theorem tstar_dstFor (R : Ranks) {du : ℕ} (hdu : 0 < du) {Ts Gam : ℝ} (hTs : 0 < Ts) (hG : 1 < Gam) :
    (dstFor R du Ts Gam / du) ^ ((1 : ℝ) / (R.f * R.k)) * Gam ^ (-(2 : ℝ) / (R.f * R.k)) = Ts := by
  have hG0 : 0 < Gam := by linarith
  have hd : ((du : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hdu.ne'
  have hn : (R.f : ℝ) * (R.k : ℝ) = ((R.f * R.k : ℕ) : ℝ) := by push_cast; ring
  unfold dstFor
  rw [mul_div_cancel_left₀ _ hd, hn, one_div, dstarOfRanks,
    Real.pow_rpow_inv_natCast (by positivity) (fk_ne R), mul_assoc, ← Real.rpow_add hG0]
  rw [show (2 : ℝ) / ((R.f * R.k : ℕ) : ℝ) + -2 / ((R.f * R.k : ℕ) : ℝ) = 0 by ring, Real.rpow_zero,
    mul_one]

def LevGap : Prop :=
  ∀ {R : Ranks} (H : Host R) (T : ℕ) [Fact T.Prime] (hlev : T ∈ H.levelPrimes) (hpde : T ≠ H.pde ∧ T ≠ H.pde')
    (pz : 𝓞 H.E) (hK : (pz : H.E) ∈ H.K) (hpz : (pz : H.E) * H.conj (pz : H.E) = (T : H.E))
    (hcong : (pz - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)}),
    (∀ i, ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (H.g i : H.E)) →
    ∃ (K : ClsPkg) (_ : ∀ i, IsEmpty (K.cls (i + 1))) (_ : K.DGam = minkM (2 * R.f * R.N R.m))
      (lat : letI := H.cmStar; ∀ i, K.cls i → Submodule (𝓞 H.E) ((hostSpacesOfNorm H T pz hpz).X i).V)
      (hlat : letI := H.cmStar; ∀ i c, Submodule.IsLattice H.E (lat i c)),
      ∀ hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol Dst hD du hdu Gam hG hwin hg ht G kb ks tw htw,
        Nonempty (LevGapD (twistRecord H hc Del hDel hgap hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw))

end Formalism.MainNotions.Inhab

end
