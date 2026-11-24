module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Objects
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v

def DegLocExact.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (N : ℕ) (M' M M'' : Type v)
    [AddCommGroup M'] [Module (Poly S N) M'] [Module S M'] [IsScalarTower S (Poly S N) M']
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    [AddCommGroup M''] [Module (Poly S N) M''] [Module S M''] [IsScalarTower S (Poly S N) M'']
    (𝓜' : GradedPMod S N M') (𝓜 : GradedPMod S N M) (𝓜'' : GradedPMod S N M'')
    (f : GradedHom 𝓜' 𝓜) (g : GradedHom 𝓜 𝓜''),
    Function.Injective f.toLin → Function.Surjective g.toLin → Function.Exact f.toLin g.toLin →
    ∀ (c : ℤ) (I : StdCell N),
      (∀ z ∈ degLoc 𝓜 c I, locMap g.toLin I.1 z = 0 →
        ∃ z' ∈ degLoc 𝓜' c I, locMap f.toLin I.1 z' = z) ∧
      (∀ z'' ∈ degLoc 𝓜'' c I, ∃ z ∈ degLoc 𝓜 c I, locMap g.toLin I.1 z = z'')

end

end GroundTheory.Heights₂.Heights.Kleiman
