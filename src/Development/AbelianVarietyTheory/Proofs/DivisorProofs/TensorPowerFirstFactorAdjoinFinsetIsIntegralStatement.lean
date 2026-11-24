module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstAndFinite
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPowerFirstFactorAdjoinFinsetIsIntegral
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.tensorPowerFirstFactorAdjoinFinset_isIntegral : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsIntegral R A] (k : ℕ) (F : Finset A), Algebra.IsIntegral R (firstAndFinite R A k F) := by
  first | (exact @GlobalTheory.EtC.firstAndFinite_isIntegral) | (exact GlobalTheory.EtC.firstAndFinite_isIntegral) | (intros; apply GlobalTheory.EtC.firstAndFinite_isIntegral  <;> assumption)
