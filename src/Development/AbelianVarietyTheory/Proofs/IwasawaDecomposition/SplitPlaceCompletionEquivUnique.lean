module

public import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

namespace GlobalTheory


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.splitPlace_completion_equiv_unique :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : _root_.ReciprocityTheory.Aut.SplitPlace L)
    (i i' : s.v.adicCompletion (NumberField.maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous i → Continuous i' →
    (∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) → (∀ x : L, i' (s.i x) = algebraMap L (s.w.adicCompletion L) x) →
    i = i' := by
  intro L _ _ _ s i i' hi hi' h h'
  have hd := HeightOneSpectrum.denseRange_algebraMap (K := NumberField.maximalRealSubfield L) s.v
  have key : (i : _ → _) = i' := by
    refine hd.equalizer hi hi' (funext fun a => ?_)
    have ha : algebraMap (NumberField.maximalRealSubfield L) (s.v.adicCompletion (NumberField.maximalRealSubfield L)) a
        = s.i (algebraMap (NumberField.maximalRealSubfield L) L a) := (s.i.commutes a).symm
    simp only [Function.comp_apply, ha, h, h']
  exact RingEquiv.ext (congrFun key)

end GlobalTheory
