module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosOkId
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorTwistRelationRowDivSwap
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.LocalRingCardinality.Params
import Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting

@[expose] public section

open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

theorem _root_.GlobalTheory.T.cofactorTwistRelation_rowDiv_swap : ∀ (R : Type) [CommRing R] (m : ℕ) (ν : Fin (m + 1) → ℕ) (a b : Fin (m + 1)) (k : ℕ) (f g : MP R (m + 1)), a ≠ b → CofRel R m ν f g → CofRel R m ν (rowDiv R a b k f) (((-1 : ℤ) ^ k) • rowDiv R b a k g) := by
  first | exact @GlobalTheory.ValCmp.cofRel_rowDiv | exact GlobalTheory.ValCmp.cofRel_rowDiv | (intros; apply GlobalTheory.ValCmp.cofRel_rowDiv <;> assumption)
