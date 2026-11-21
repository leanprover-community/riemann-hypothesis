import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.DualFlatOf
import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideFinal
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FinrankTensor

section
open MvPolynomial

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems Formalism.L2.G.Model

def PosCoreLetterAt : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ jO w →
    ∀ (m d : ℕ) (vec : Bool), 1 ≤ m →
      ∃ β : ↥(dualWeyl Kf (m + 1) (m + 1) (nuOf (letterWt m d vec))) ≃ₗ[Kf]
          Module.Dual Kf ↥(dualWeyl Kf (m + 1) (m + 1) (nuOf (letterWt m d vec))),
        PosCore O Kf p m (letterWt m d vec) (m * Nat.log p d) β

theorem letterWt_anti (m d : ℕ) (vec : Bool) : Antitone (letterWt m d vec) := by
  intro i j hij
  have hl : i = Fin.last m → j = Fin.last m := fun hi => le_antisymm (Fin.le_last j) (hi ▸ hij)
  have h0 : j = 0 → i = 0 := fun hj => le_antisymm (hj ▸ hij) (Fin.zero_le i)
  unfold letterWt
  cases vec
  · simp only [Bool.false_eq_true, if_false]
    by_cases hj : j = Fin.last m
    · by_cases hi : i = Fin.last m
      · simp [hi, hj]
      · simp [hi, hj]
    · have hi : i ≠ Fin.last m := fun hi => hj (hl hi)
      simp [hi, hj]
  · simp only [if_true]
    by_cases hj : j = 0
    · simp [hj, h0 hj]
    · by_cases hi : i = 0
      · simp [hi, hj]
      · simp [hi, hj]

def kapTenW (p : ℕ) {n' : ℕ} (m : ℕ) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) : ℕ :=
  ∑ x : TT × Bool, expN p m (hhWt m TT aT bT x)

def DualLatWAt : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ jO w →
    ∀ (m : ℕ) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ), 1 ≤ m →
    ∃ Ψ : Module.Dual Kf ↥(VHH (m := m) Kf TT aT bT) ≃ₗ[Kf] ↥(VHH (m := m) Kf TT aT bT),
      (∀ L : Submodule W (Fin (m + 1) → Qq), IsLattice W L →
        (Formalism.GradedWeylDivisibility.dualLat O Kf (HHL (O := O) ι σ TT aT bT L)).map (Ψ.toLinearMap.restrictScalars O) ≤
                  HHL ι σ TT aT bT (latDual L) ∧
        scale ((p : Kf) ^ (kapTenW p m TT aT bT : ℤ)) (HHL (O := O) ι σ TT aT bT (latDual L)) ≤
          (Formalism.GradedWeylDivisibility.dualLat O Kf (HHL (O := O) ι σ TT aT bT L)).map (Ψ.toLinearMap.restrictScalars O)) ∧
      ∀ e : Edge W Qq (m + 1), IsEdge p n' 1 e →
        (ReHH' p ι σ w TT aT bT e).map (Ψ.toLinearMap.restrictScalars O) ≤ ReHH p ι σ w TT aT bT e.dual ∧
        scale ((p : Kf) ^ (kapTenW p m TT aT bT : ℤ)) (ReHH p ι σ w TT aT bT e.dual) ≤
          (ReHH' p ι σ w TT aT bT e).map (Ψ.toLinearMap.restrictScalars O)

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.L2.G.Model

def SharpFormAt : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ jO w →
    ∀ (m d : ℕ) (vec : Bool), 1 ≤ m →
    ∃ B : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf →ₗ[Kf] MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf →ₗ[Kf] Kf,
      (∀ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (P Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf),
        B (rowAct Kf g P) Q = B P (rowAct Kf g.transpose Q)) ∧
      (∀ Q ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf (letterWt m d vec)),
        (∀ P ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf (letterWt m d vec)), B P Q = 0) → Q = 0) ∧
      (∀ Q ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf (letterWt m d vec)),
        (∀ P ∈ nabO O Kf m (nuOf (letterWt m d vec)), B P Q ∈ Set.range (algebraMap O Kf)) →
          Q ∈ nabO O Kf m (nuOf (letterWt m d vec))) ∧
      (∀ Q ∈ nabO O Kf m (nuOf (letterWt m d vec)), ∀ P ∈ nabO O Kf m (nuOf (letterWt m d vec)),
        B P (((p : Kf) ^ (m * Nat.log p d)) • Q) ∈ Set.range (algebraMap O Kf))

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.L2.G.Model Formalism.L2.G.Model.TS

def SharpDAt : Prop :=
  ∀ (p : ℕ) (O Kf : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    [IsFractionRing O Kf] [CharZero Kf], p.Prime → ¬ IsUnit ((p : ℕ) : O) →
    ∀ (m d : ℕ) (vec : Bool), 1 ≤ m →
    ∀ Q ∈ Formalism.L2.G.Model.nabO O Kf m (nuOf (letterWt m d vec)), ∀ P ∈ Formalism.L2.G.Model.nabO O Kf m (nuOf (letterWt m d vec)),
      (fockR (hw Kf (le_refl (m + 1)) (nuOf (letterWt m d vec))) (hw Kf (le_refl (m + 1)) (nuOf (letterWt m d vec))))⁻¹ *
        fockR P (((p : Kf) ^ (m * Nat.log p d)) • Q) ∈ Set.range (algebraMap O Kf)

def SettingCharZeroAt : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ jO w → CharZero Kf ∧ ¬ IsUnit ((p : ℕ) : O)

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem settingCZ : SettingCharZeroAt := by
  unfold SettingCharZeroAt
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS
  have hpW : ¬IsUnit (p : W) := hS.p_unif.1

  have hW : CharZero W := by
    rcases CharP.char_is_prime_or_zero W (ringChar W) with hq | hq
    · exfalso
      haveI hcp : CharP W (ringChar W) := ringChar.charP W
      by_cases hqp : ringChar W = p
      · apply hS.p_unif.ne_zero
        rw [← hqp]
        exact CharP.cast_eq_zero W (ringChar W)
      · have hcop : Nat.Coprime p (ringChar W) :=
          (Nat.coprime_primes hS.prime hq).mpr (Ne.symm hqp)
        apply hpW
        have hu : IsUnit (p : ZMod (ringChar W)) := by
          rw [← ZMod.coe_unitOfCoprime p hcop]
          exact Units.isUnit _
        have hu' := hu.map (ZMod.castHom (dvd_refl (ringChar W)) W)
        simpa using hu'
    · haveI : CharP W 0 := by
        rw [← hq]
        exact ringChar.charP W
      exact CharP.charP_to_charZero W
  haveI := hS.frac_alt
  have hQ : CharZero Qq := charZero_of_injective_algebraMap (IsFractionRing.injective W Qq)
  have hK : CharZero Kf := (RingHom.charZero_iff ι.injective).mp hQ

  have hpO : ¬IsUnit (p : O) := by
    intro hu
    have hint : jO.IsIntegral := RingHom.IsIntegral.of_finite hS.finite
    have hmax : ((IsLocalRing.maximalIdeal O).comap jO).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' jO hint (IsLocalRing.maximalIdeal O)
    have hle : (IsLocalRing.maximalIdeal O).comap jO = IsLocalRing.maximalIdeal W :=
      IsLocalRing.eq_maximalIdeal hmax
    have hpm : (p : W) ∈ IsLocalRing.maximalIdeal W := (IsLocalRing.mem_maximalIdeal _).mpr hpW
    rw [← hle, Ideal.mem_comap, map_natCast] at hpm
    exact (IsLocalRing.mem_maximalIdeal _).mp hpm hu
  exact ⟨hK, hpO⟩

end Formalism.MainNotions.ColumnSystems.Pf
end
end
