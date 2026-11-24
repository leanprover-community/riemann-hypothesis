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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def GradedPres.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (N : ℕ) (M : Type (max u v))
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (𝓜 : GradedPMod S N M), Module.Finite (Poly S N) M →
    ∃ (F : Type (max u v)) (_ : AddCommGroup F) (_ : Module (Poly S N) F) (_ : Module S F)
      (_ : IsScalarTower S (Poly S N) F) (K : Type (max u v)) (_ : AddCommGroup K)
      (_ : Module (Poly S N) K) (_ : Module S K) (_ : IsScalarTower S (Poly S N) K)
      (𝓕 : GradedPMod S N F) (𝓚 : GradedPMod S N K) (r : ℕ) (b : Module.Basis (Fin r) (Poly S N) F)
      (d : Fin r → ℤ) (f : GradedHom 𝓚 𝓕) (g : GradedHom 𝓕 𝓜),
      (∀ j, b j ∈ 𝓕.piece (d j)) ∧ Module.Finite (Poly S N) K ∧ Function.Injective f.toLin ∧
        Function.Surjective g.toLin ∧ Function.Exact f.toLin g.toLin

def GradedULift.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (N : ℕ) (M : Type v)
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (𝓜 : GradedPMod S N M),
    ∃ (M' : Type (max u v)) (_ : AddCommGroup M') (_ : Module (Poly S N) M') (_ : Module S M')
      (_ : IsScalarTower S (Poly S N) M') (𝓜' : GradedPMod S N M') (f : GradedHom 𝓜 𝓜')
      (g : GradedHom 𝓜' 𝓜), Function.LeftInverse g.toLin f.toLin ∧ Function.RightInverse g.toLin f.toLin

def CohomRetract.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (N : ℕ) (M : Type v) (M' : Type w)
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    [AddCommGroup M'] [Module (Poly S N) M'] [Module S M'] [IsScalarTower S (Poly S N) M']
    (𝓜 : GradedPMod S N M) (𝓜' : GradedPMod S N M') (f : GradedHom 𝓜 𝓜') (g : GradedHom 𝓜' 𝓜),
    Function.LeftInverse g.toLin f.toLin → ∀ (i : ℕ) (c : ℤ), Function.Injective (cohomMap f i c)

section Hypotheses

variable (k : Type u) [Field k] (N : ℕ)

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
