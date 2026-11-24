module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexMatrixGaussSumNormIntegralGaloisStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical



namespace GlobalTheory.GaussUnit

theorem isIntegral_of_eq {x y : ℂ} (h : IsIntegral ℤ x) (e : y = x) : IsIntegral ℤ y := e ▸ h

theorem unitOff_of_two {N : ℕ} {u : ℂ} (h0 : u ≠ 0) {a b : ℕ} (ha : IsIntegral ℤ ((N : ℂ) ^ a * u))
    (hb : IsIntegral ℤ ((N : ℂ) ^ b * u⁻¹)) : UnitOff N u := by
  have hN : ∀ c : ℕ, IsIntegral ℤ ((N : ℂ) ^ c) := fun c => by
    have : IsIntegral ℤ ((N : ℕ) : ℂ) := by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (N : ℤ)))
    exact this.pow c
  refine ⟨h0, a + b, ?_, ?_⟩
  · have := (hN b).mul ha
    refine isIntegral_of_eq (this) ?_
    ring
  · have := (hN a).mul hb
    refine isIntegral_of_eq (this) ?_
    ring

theorem unitOff_one (N : ℕ) : UnitOff N 1 :=
  unitOff_of_two (a := 0) (b := 0) one_ne_zero (by simpa using isIntegral_one) (by simpa using isIntegral_one)

theorem unitOff_mul {N : ℕ} {u v : ℂ} (hu : UnitOff N u) (hv : UnitOff N v) : UnitOff N (u * v) := by
  obtain ⟨hu0, a, ha, ha'⟩ := hu
  obtain ⟨hv0, b, hb, hb'⟩ := hv
  refine ⟨mul_ne_zero hu0 hv0, a + b, ?_, ?_⟩
  · refine isIntegral_of_eq (ha.mul hb) ?_
    ring
  · refine isIntegral_of_eq (ha'.mul hb') ?_
    rw [mul_inv]
    ring

theorem unitOff_prod {N : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, UnitOff N (f i)) :
    UnitOff N (∏ i ∈ s, f i) :=
  Finset.prod_induction f (UnitOff N) (fun _ _ => unitOff_mul) (unitOff_one N) h

theorem unitOff_normalised {N q n r : ℕ} (hq : q ≠ 0) {m : ℕ} (hd : q ∣ N ^ m) (hrn : r ≤ n) {S : ℂ}
    (h1 : ‖S‖ ^ 2 = (q : ℝ) ^ (r ^ 2)) (h2 : IsIntegral ℤ S) (h3 : IsIntegral ℤ ((q : ℂ) ^ (r ^ 2) * S⁻¹)) :
    UnitOff N (((q : ℂ) ^ (n * r))⁻¹ * S) := by
  have hI : ∀ c : ℕ, IsIntegral ℤ ((c : ℕ) : ℂ) := fun c => by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (c : ℤ)))
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hS : S ≠ 0 := by
    rintro rfl
    have : (0 : ℝ) < (q : ℝ) ^ (r ^ 2) := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hq) _
    rw [← h1] at this
    simp at this
  obtain ⟨c, hc⟩ := hd
  have hcC : (N : ℂ) ^ m = q * c := by exact_mod_cast hc
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrn
  refine unitOff_of_two (a := m * ((r + d) * r)) (b := 0) (mul_ne_zero (inv_ne_zero (pow_ne_zero _ hqC)) hS) ?_ ?_
  · refine isIntegral_of_eq (((hI c).pow ((r + d) * r)).mul h2) ?_
    rw [pow_mul, hcC, mul_pow]
    field_simp
  · refine isIntegral_of_eq (((hI q).pow (d * r)).mul h3) ?_
    rw [mul_inv, inv_inv]
    ring

theorem card_dvd_pow (k : Type) [Field k] [Fintype k] {N : ℕ} (hN : (N : k) = 0) : ∃ m, Fintype.card k ∣ N ^ m := by
  obtain ⟨p, hp⟩ := CharP.exists k
  obtain ⟨m, -, hm⟩ := FiniteField.card k p
  exact ⟨m, hm ▸ pow_dvd_pow_of_dvd ((CharP.cast_eq_zero_iff k p N).mp hN) _⟩

theorem unitOff_prod_gaussSum : ∀ (D : D7) [∀ PP : Pl D.host.E, Fintype (kP PP)] (Q : Finset (Pl D.host.E)) (n r : ℕ), r ≤ n → ∀ (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), (∀ PP ∈ Q, (ψP PP).IsPrimitive) → (∀ PP ∈ Q, ξ PP ≠ 1) → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) → UnitOff N (∏ PP ∈ Q.attach, ((Nat.card (kP PP.1) : ℂ) ^ (n * r))⁻¹ * ∑ g : GL (Fin r) (kP PP.1), (((ξ PP.1 (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) * ψP PP.1 (Matrix.trace (g : Matrix (Fin r) (Fin r) (kP PP.1)))) := by
  intro D _ Q n r hrn ψP ξ hψ hξ N _ hN
  refine unitOff_prod _ _ ?_
  rintro ⟨PP, hPP⟩ -
  haveI := PP.isMaximal
  letI : Field (kP PP) := Ideal.Quotient.field PP.asIdeal
  have h0 : (N : kP PP) = 0 := by
    have := Ideal.Quotient.eq_zero_iff_mem.mpr (hN PP hPP)
    simpa using this
  obtain ⟨m, hm⟩ := card_dvd_pow (kP PP) h0
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.T.galois_matrix_gaussSum_eq_char_pow_mul (kP PP) (ψP PP) (ξ PP) r (hψ PP hPP) (hξ PP hPP) _ rfl
  rw [Nat.card_eq_fintype_card]
  exact unitOff_normalised Fintype.card_ne_zero hm hrn h1 h2 h3

end GlobalTheory.GaussUnit
