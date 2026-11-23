module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField Formalism.MainNotions.S
open scoped TensorProduct

namespace Formalism.L2.SG.Pf

def PsiTrCore : Prop :=
  ∀ (I : AutInst) (ψ : I.E ⊗[I.F] Af I.F → ℂ), (∀ x y, ψ (x + y) = ψ x * ψ y) →
    (∀ x ∈ IntAf I.F I.E, ψ x = 1) →
    (∀ x : I.E, ψ (Formalism.UG.inclE (F := I.F) (Af I.F) x) *
      ∏ v, Complex.exp (2 * Real.pi * Complex.I * (I.φ v x + star (I.φ v x))) = 1) →
    ∀ y : I.E, (∀ o : 𝓞 I.E, ∃ m : ℤ, Algebra.trace ℚ I.E ((o : I.E) * y) = m) →
      ∀ t ∈ IntAf I.F I.E, ψ (t * Formalism.UG.inclE (F := I.F) (Af I.F) y) = 1

def DdTraceCore : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    ∀ y ∈ ((((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (differentIdeal ℤ (𝓞 F)) : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E))⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E),
      ∀ o : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E ((o : E) * y) = m

end Formalism.L2.SG.Pf
