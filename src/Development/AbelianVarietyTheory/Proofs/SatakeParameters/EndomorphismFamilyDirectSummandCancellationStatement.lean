module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EndomorphismFamilyDirectSummandCancellation
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

@[expose] public section


theorem _root_.GlobalTheory.T.endomorphismFamily_direct_summand_cancellation : ∀ (k ι V V' U : Type) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V] [AddCommGroup V'] [Module k V'] [FiniteDimensional k V'] [AddCommGroup U] [Module k U] [FiniteDimensional k U] (a : ι → Module.End k V) (b : ι → Module.End k V') (c : ι → Module.End k U), (∃ e : (V × U) ≃ₗ[k] (V' × U), ∀ i x, e ((a i).prodMap (c i) x) = (b i).prodMap (c i) (e x)) → ∃ e : V ≃ₗ[k] V', ∀ i x, e (a i x) = b i (e x) := by
  first | exact @GlobalTheory.endFamily_cancel | exact GlobalTheory.endFamily_cancel | (intros; apply GlobalTheory.endFamily_cancel <;> assumption)
