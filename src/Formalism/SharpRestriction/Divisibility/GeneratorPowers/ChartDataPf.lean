module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ChartSer
public import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.TB.Canon
open scoped CategoryTheory.Obj

private theorem mem_degLE_lemma {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (e : κ →₀ ℕ) :
    e ∈ degLE m ↔ Finsupp.degree e ≤ m := by
  constructor
  · intro he
    simp [degLE] at he
    exact he.2
  · intro hd
    have hle : ∀ i, e i ≤ m := by
      intro i
      refine le_trans ?_ hd
      by_cases hi : i ∈ e.support
      · exact Finset.single_le_sum (f := fun j => e j) (fun j _ => Nat.zero_le _) hi
      · have h0 : e i = 0 := by simpa using hi
        omega
    simp [degLE]
    refine ⟨⟨fun i => ⟨e i, Nat.lt_succ_of_le (hle i)⟩, ?_⟩, hd⟩
    ext i
    simp

theorem mk_psTrunc {S : Type} [CommRing S] {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ S)
    (hf : MvPowerSeries.constantCoeff f = 0) :
    Chart.pj m f = Ideal.Quotient.mk _ (psTrunc m f - MvPolynomial.C (MvPolynomial.constantCoeff (psTrunc m f))) := by
  have h0 : MvPolynomial.constantCoeff (psTrunc m f) = 0 := by

    simp only [psTrunc, map_sum, MvPolynomial.constantCoeff_monomial]
    refine Finset.sum_eq_zero fun x _ => ?_
    split_ifs with hx
    · rw [hx, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf]
    · rfl
  rw [h0, map_zero, sub_zero]
  unfold Chart.pj
  congr 1
  ext e
  simp only [psTrunc, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with he
  · have hd : Finsupp.degree e ≤ m := (mem_degLE_lemma m e).1 he
    rw [MvPowerSeries.coeff_truncTotal]
    omega
  · have hd : ¬ Finsupp.degree e ≤ m := fun h => he ((mem_degLE_lemma m e).2 h)
    first
      | rw [MvPowerSeries.coeff_truncTotal_eq_zero]; omega
      | simp [MvPowerSeries.truncTotal, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]; omega

theorem jetMap_zR {S : Type} [CommRing S] {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (h) (s : κ) :
    (jetMap φ h : Jet S κ m →ₐ[S] Jet S κ' m) (Ideal.Quotient.mk _ (MvPolynomial.X s)) = Ideal.Quotient.mk _ (φ s) := by
  simp only [jetMap]
  show ((Ideal.Quotient.mkₐ S (orig S κ' ^ (m + 1))).comp (MvPolynomial.bind₁ φ)) (MvPolynomial.X s) = _
  simp [MvPolynomial.bind₁_X_right]

end Formalism.MainNotions.ModuliIntegralCharts.H1
