import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyOfPowerTraces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DenseSplitFrobenius
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeIffLocalComponentSatakeStatement

section
namespace GlobalTheory.NormDivisibility

open NumberField IsDedekindDomain

theorem natCast_eq_zero_of_dvd_card {R : Type*} [CommRing R] [IsDomain R] [Finite R] {l : ℕ}
    (hl : l.Prime) (h : l ∣ Nat.card R) : (l : R) = 0 := by
  classical
  have := Fintype.ofFinite R
  let _ : Field R := Fintype.fieldOfDomain R

  obtain ⟨n, hp, hc⟩ := FiniteField.card R (ringChar R)
  rw [Nat.card_eq_fintype_card, hc] at h
  rw [(Nat.prime_dvd_prime_iff_eq hl hp).mp (hl.dvd_of_dvd_pow h)]
  exact ringChar.Nat.cast_ringChar

theorem not_dvd_norm_of_not_mem {E : Type} [Field E] [NumberField E] {l : ℕ} (hl : Nat.Prime l)
    (w : HeightOneSpectrum (RingOfIntegers E))
    (hw : (l : RingOfIntegers E) ∉ w.asIdeal) : ¬ l ∣ Formalism.ConjugateSelfDual.normV w := by
  intro h
  have : Finite (RingOfIntegers E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  unfold Formalism.ConjugateSelfDual.normV at h
  have h0 := natCast_eq_zero_of_dvd_card (R := RingOfIntegers E ⧸ w.asIdeal) hl h
  apply hw
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h0

end GlobalTheory.NormDivisibility
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

namespace GlobalTheory.FrobOps
open Polynomial

theorem not_dvd_normV {E : Type} [Field E] [NumberField E] {l : ℕ} (hl : l.Prime) (w : HeightOneSpectrum (𝓞 E))
    (h : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) : ¬ l ∣ normV w := by
  first
  | exact @_root_.GlobalTheory.NormDivisibility.not_dvd_norm_of_not_mem
  | exact _root_.GlobalTheory.NormDivisibility.not_dvd_norm_of_not_mem
  | (apply _root_.GlobalTheory.NormDivisibility.not_dvd_norm_of_not_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormDivisibility.not_dvd_norm_of_not_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormDivisibility.not_dvd_norm_of_not_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormDivisibility.not_dvd_norm_of_not_mem ..)

theorem norm_le_one {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (m : ℤ) (q e : ℕ) (hq : ¬ l ∣ q) :
    ‖ι.symm ((m : ℂ) / (q : ℂ) ^ e)‖ ≤ 1 := by
  rw [map_div₀, map_pow, map_intCast, map_natCast, norm_div, norm_pow]
  have h1 : ‖((q : ℕ) : Qbar l)‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), PadicAlgCl.norm_extends, Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hq
  rw [h1, one_pow, div_one]
  exact IsUltrametricDist.norm_intCast_le_one _ m

theorem trace_pow_of_charpoly {a : ℕ} (M : Matrix (Fin a) (Fin a) ℂ) (B : Multiset ℂ)
    (h : M.charpoly = (B.map fun b => X - C b).prod) (n : ℕ) : (M ^ n).trace = (B.map (· ^ n)).sum := by
  rw [Matrix.trace_eq_sum_roots_charpoly, GlobalTheory.CharpolyPow.roots_charpoly_pow, h, Polynomial.roots_multiset_prod_X_sub_C]

theorem iota_trc {Γ : Type} [Group Γ] {l : ℕ} [Fact l.Prime] {a : ℕ} (ι : Qbar l ≃+* ℂ) (r : Γ →* GL (Fin a) (Qbar l))
    (s : Γ) (n : ℕ) :
    ι (trc r (s ^ n)) = ((((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).map ι.toRingHom) ^ n).trace := by
  rw [← Matrix.map_pow, trc, map_pow, Units.val_pow_eq_pow_val, Matrix.trace, Matrix.trace, map_sum]
  rfl

end GlobalTheory.FrobOps
end
end
