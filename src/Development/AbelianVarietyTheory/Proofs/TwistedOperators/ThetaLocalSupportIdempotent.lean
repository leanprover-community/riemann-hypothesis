module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisOSumSmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.SplitVacAlg

open GlobalTheory.MovedAlg

theorem isAlg_sqrt_inv (n : ℕ) : IsAlgebraic ℚ (((Real.sqrt (n : ℝ) : ℝ) : ℂ)⁻¹) := by
  have h : IsAlgebraic ℚ (((Real.sqrt (n : ℝ) : ℝ) : ℂ)) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (n : ℚ), Polynomial.X_pow_sub_C_ne_zero (by norm_num) _, ?_⟩
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, eq_ratCast, Rat.cast_natCast]
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    simp
  rw [← mem_algebraicClosure_iff] at h ⊢
  exact inv_mem h

section Comb

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f₀ : WO S T → ℂ}

theorem isAlgComb_heis {u : WO S T} (hu : u.map (infPart D) = 0) : IsAlgComb ψ S T f₀ (heisO ψ S T u f₀) :=
  ⟨1, fun _ => 1, fun _ => u, fun _ => isAlgebraic_one, fun _ => hu, by simp⟩

theorem isAlgComb_sum (Δ : Finset (WO S T)) (hΔ : ∀ u ∈ Δ, u.map (infPart D) = 0) :
    IsAlgComb ψ S T f₀ (∑ u ∈ Δ, heisO ψ S T u f₀) := by
  classical
  induction Δ using Finset.induction_on with
  | empty => simpa using (IsAlgComb.zero : IsAlgComb ψ S T f₀ 0)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (isAlgComb_heis (hΔ a (Finset.mem_insert_self a s))).add
      (ih fun u hu => hΔ u (Finset.mem_insert_of_mem hu))

theorem isAlgComb_self : IsAlgComb ψ S T f₀ f₀ := by
  have := isAlgComb_heis (ψ := ψ) (f₀ := f₀) (u := (0 : WO S T)) (by simp)
  rwa [GlobalTheory.SplitScalar.heisO_zero ψ S T f₀] at this

end Comb


end GlobalTheory.SplitVacAlg

end
