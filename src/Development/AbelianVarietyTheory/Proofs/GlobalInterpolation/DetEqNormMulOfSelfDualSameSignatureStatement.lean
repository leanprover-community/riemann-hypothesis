module

public import Formalism.LocalRingCardinality.DataSpaces
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DetEqNormMulOfSelfDualSameSignature
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] IsCMField.starRing

theorem _root_.GlobalTheory.T.det_eq_norm_mul_of_selfDual_same_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ W₁ W₂ : HSpace E, W₁.SigOK → W₂.SigOK → W₁.rank = W₂.rank → (∀ τ, W₁.sig τ = W₂.sig τ) → ∃ z : E, W₂.gram.det = z * star z * W₁.gram.det := by
  first | exact @GlobalTheory.SelfDualDet.det_eq_norm_mul | exact GlobalTheory.SelfDualDet.det_eq_norm_mul | (intros; apply GlobalTheory.SelfDualDet.det_eq_norm_mul <;> assumption)
