module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

namespace GlobalTheory.QLog

theorem defect_sum {O E : Type} [CommRing O] [CommRing E] [Algebra O E] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, constantCoeff (μ i) = 0) (m : ℕ)
    {ι : Type} [Fintype ι] (a : ι → E) (f : ι → MvPowerSeries (Fin d) E) :
    defect μ m (∑ i, a i • f i) = ∑ i, a i • defect μ m (f i) := by

  simp only [defect, ← coe_substAlgHom (hasSubst_up_nmul (Q := E) hμ m), map_sum, map_smul,
  Finset.smul_sum, smul_sub, Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

theorem map_sum_smul {O E : Type} [CommRing O] [CommRing E] [Algebra O E] {σ : Type}
    {ι : Type} [Fintype ι] (b : ι → O) (s : ι → MvPowerSeries σ O) :
    map (algebraMap O E) (∑ i, b i • s i) = ∑ i, algebraMap O E (b i) • map (algebraMap O E) (s i) := by

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext α
  rw [coeff_map, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_smul, coeff_map]
  simp only [smul_eq_mul, map_mul]

theorem Chart.isLie_comb : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) E) (l : ι → G.dual.Lie) (b : ι → O), (∀ i, QL c.μ ⊤ (e i)) → (∀ i, c.IsLie (e i) (l i)) → c.IsLie (comb b e) (∑ i, b i • l i) := by
  intro p _ O E _ _ _ hF G d c ι _ e l b _ hl
  have hinj : Function.Injective (algebraMap O E) := hF.inj
  rw [c.isLie_iff hinj]
  intro n
  choose s hs hc using fun i => (c.isLie_iff hinj _ _).1 (hl i) n
  refine ⟨∑ i, b i • s i, ?_, fun w φ hφ => ?_⟩
  · rw [map_sum_smul, comb, defect_sum c.isLaw.const]
    exact Finset.sum_congr rfl fun i _ => by rw [hs i]
  · have : (∑ i, b i • l i) w - φ (c.ev n (∑ i, b i • s i)) =
        ∑ i, b i * (l i w - φ (c.ev n (s i))) := by

      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
      smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
    rw [this]
    exact Finset.dvd_sum fun i _ => dvd_mul_of_dvd_right (hc i w φ hφ) _

end GlobalTheory.QLog
