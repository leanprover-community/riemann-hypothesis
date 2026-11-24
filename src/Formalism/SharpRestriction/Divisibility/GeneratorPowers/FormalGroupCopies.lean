module

public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PartialDerivativeExponent

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies

open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent

variable {R : Type} [CommRing R] {d n : ℕ}

theorem dofN_mul_left (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (A B : PS R n d)
    (hA : ∀ j, pderiv (R := R) (b, j) A = 0) : DofN F b u (A * B) = A * DofN F b u B := by
  unfold DofN
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Derivation.leibniz, hA j, smul_zero, add_zero, smul_eq_mul]
  ring

section Fold

variable {ι : Type} [Fintype ι] (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)

theorem dmon_zero (g : PS R n d) : DmonN F cp u 0 g = g := by
  simp [DmonN]

theorem dpoly_sup (P : MvPolynomial ι R) (T : Finset (ι →₀ ℕ)) (hT : P.support ⊆ T)
    (g : PS R n d) : DpolyN F cp u P g = ∑ mm ∈ T, C (P.coeff mm) * DmonN F cp u mm g := by
  unfold DpolyN
  apply Finset.sum_subset hT
  intro mm _ hmm
  have h0 : P.coeff mm = 0 := by simpa [MvPolynomial.mem_support_iff] using hmm
  rw [h0, map_zero, zero_mul]

theorem dpoly_add (P Q : MvPolynomial ι R) (g : PS R n d) :
    DpolyN F cp u (P + Q) g = DpolyN F cp u P g + DpolyN F cp u Q g := by
  classical
  rw [dpoly_sup F cp u (P + Q) (P.support ∪ Q.support) MvPolynomial.support_add,
    dpoly_sup F cp u P (P.support ∪ Q.support) Finset.subset_union_left,
    dpoly_sup F cp u Q (P.support ∪ Q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun mm _ => ?_)
  rw [MvPolynomial.coeff_add, map_add (f := _), add_mul]

theorem dpoly_monomial (mm : ι →₀ ℕ) (a : R) (g : PS R n d) :
    DpolyN F cp u (MvPolynomial.monomial mm a) g = C a * DmonN F cp u mm g := by
  classical
  rw [dpoly_sup F cp u _ {mm} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl]

def dpolyHom (g : PS R n d) : MvPolynomial ι R →+ PS R n d where
  toFun P := DpolyN F cp u P g
  map_zero' := by simp [DpolyN]
  map_add' P Q := dpoly_add F cp u P Q g

end Fold

end Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies

end Formalism.MainNotions.ModuliIntegralCharts.H1
