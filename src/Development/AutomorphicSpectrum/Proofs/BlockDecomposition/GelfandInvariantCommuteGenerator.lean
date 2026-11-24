module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix Finset
open PositivityTheory.RgBcC.RealD (epow gelA)

namespace GlobalTheory.CompanionTheory.ModelS

theorem epow_eq_pow_of {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) (a b : Fin n) :
    epow E m a b = ((Matrix.of E : Matrix (Fin n) (Fin n) (Module.End ℂ V)) ^ m) a b := by
  induction m generalizing a b with
  | zero =>
      change (if a = b then 1 else 0) = _
      simp only [pow_zero, Matrix.one_apply]
  | succ m ih =>
      change (∑ c, E a c * epow E m c b) = _
      simp only [pow_succ', Matrix.mul_apply, Matrix.of_apply, ih]

theorem gelA_central : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel E →
    ∀ (m : ℕ) (a b : Fin n), gelA E m * E a b = E a b * gelA E m := by
  intro n V _ _ E hE m a b
  rw [eq_comm, ← sub_eq_zero]
  delta gelA
  simp only [epow_eq_pow_of]
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [GlobalTheory.SmoothForms.comm_pow_of_apply E hE, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, sub_self]

end GlobalTheory.CompanionTheory.ModelS
