module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistMulDegreeZeroLocallySurjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.tateTwist_mul_degreeZero_locally_surjective : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {K : Cx (ZMod q)} (τ : Pair (sgl (tw q i)) (sgl (tw q j)) K), τ.IsTensor → ∀ φ : tw q k ⟶ K.X 0, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map φ (twGen k ζ) = τ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) → ∀ (U : Scheme.{0}) (y : Sec (K.X 0) U), Loc U fun V g => ∃ z : Sec (tw q k) V, Sec.map φ z = Sec.res g y := by
  first | (exact @GlobalTheory.EtC.tw_mul_locSurj) | (exact GlobalTheory.EtC.tw_mul_locSurj) | (intros; apply GlobalTheory.EtC.tw_mul_locSurj  <;> assumption)
