module

public import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal
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

noncomputable section

namespace Formalism.L2.LamCM

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

def IsBaseChangeLine {K K1 : Type} [Field K] [NumberField K] [Field K1] [NumberField K1] [Algebra K K1] (L : MLine K)
    (L1 : MLine K1) : Prop :=
  ((L1.I : Submodule (𝓞 K1) K1) = Submodule.span (𝓞 K1) (algebraMap K K1 '' {x | x ∈ L.I})) ∧
  ∀ σ : K1 →+* ℂ, L1.n σ = L.n (σ.comp (algebraMap K K1))

def NdegBaseChange : Prop :=
  ∀ (K K1 : Type) [Field K] [NumberField K] [Field K1] [NumberField K1] [Algebra K K1] (L : MLine K) (L1 : MLine K1),
    L.Good → IsBaseChangeLine L L1 → L1.Good ∧ L1.ndeg = L.ndeg

def LocGenBaseChange : Prop :=
  ∀ (K K1 : Type) [Field K] [NumberField K] [Field K1] [NumberField K1] [Algebra K K1] (L : MLine K) (L1 : MLine K1)
    (p : HeightOneSpectrum (𝓞 K)) (p1 : HeightOneSpectrum (𝓞 K1)) (c : K), L.I ≠ 0 → IsBaseChangeLine L L1 →
    (∀ a : 𝓞 K, a ∈ p.asIdeal ↔ (algebraMap (𝓞 K) (𝓞 K1) a) ∈ p1.asIdeal) → IsLocGen p c L.I →
    IsLocGen p1 (algebraMap K K1 c) L1.I

end Formalism.L2.LamCM
