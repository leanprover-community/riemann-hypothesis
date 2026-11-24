module

public import Formalism.PeriodIntegrals.BlockRatReal
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylMap
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylRowStable
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowDivStable
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.SumIcoTsubTelescope
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.WeylLeDual
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial Matrix

noncomputable section

namespace PI.BlockRatReal.UnitaryGroupMassFormula

theorem s1 {S : Type} [CommRing S] (φ : ℤ →+* S) (k : ℕ) (ν : Fin k → ℕ) (hν : Antitone ν)
    (f : MvPolynomial (Fin k × Fin k) ℤ) (hf : f ∈ PI.BlockRatReal.weyl ℤ k k le_rfl ν) :
    MvPolynomial.map φ f ∈ PI.BlockRatReal.dualWeyl S k k ν := by
  have hle := Formalism.GradedWeylDivisibility.weylLeDual_of Formalism.GradedWeylDivisibility.highestWeightVectorMem Formalism.GradedWeylDivisibility.dualWeylModuleRowDividedPowerStable
  have h1 : f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℤ k k ν := hle ℤ k k le_rfl ν hν hf
  exact Formalism.GradedWeylDivisibility.dualWeylModuleMap ℤ S φ k k ν f h1

theorem s2 {R : Type} [CommRing R] (k : ℕ) (ν : Fin k → ℕ) (g : Matrix (Fin k) (Fin k) R)
    (f : MvPolynomial (Fin k × Fin k) R) (hf : f ∈ PI.BlockRatReal.dualWeyl R k k ν) :
    Formalism.GradedWeylDivisibility.rowAct R g f ∈ PI.BlockRatReal.dualWeyl R k k ν := by
  have h1 : f ∈ Formalism.GradedWeylDivisibility.dualWeyl R k k ν := hf
  exact Formalism.GradedWeylDivisibility.dualWeylModuleRowActionStable R k k ν g f h1

theorem eval_map_rowAct {LL : Type} [Field LL] (φ : LL →+* ℂ) {k : ℕ} (g : Matrix (Fin k) (Fin k) LL)
    (F : MvPolynomial (Fin k × Fin k) LL) (z : Matrix (Fin k) (Fin k) ℂ) :
    eval (fun x => z x.1 x.2) (MvPolynomial.map φ (Formalism.GradedWeylDivisibility.rowAct LL g F)) =
      eval (fun x => (g.map φ * z) x.1 x.2) (MvPolynomial.map φ F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [Formalism.GradedWeylDivisibility.rowAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp]
    congr 1
    simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.mul_apply]

theorem map_map_int {LL : Type} [Field LL] (φ : LL →+* ℂ) {σ : Type} (f : MvPolynomial σ ℤ) :
    MvPolynomial.map φ (MvPolynomial.map (Int.castRingHom LL) f) = MvPolynomial.map (Int.castRingHom ℂ) f := by
  rw [MvPolynomial.map_map, RingHom.ext_int (φ.comp (Int.castRingHom LL)) (Int.castRingHom ℂ)]

end PI.BlockRatReal.UnitaryGroupMassFormula
