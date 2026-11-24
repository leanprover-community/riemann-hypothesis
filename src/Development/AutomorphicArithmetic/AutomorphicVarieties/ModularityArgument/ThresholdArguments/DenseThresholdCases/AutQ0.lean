module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AAcrossOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.IsAutCsdA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep UpperTheory.V.Af
namespace UpperTheory.GalN.V
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
section Conv
variable {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)}
theorem mkCsd'_alt [IsCMField F] (h : AutCsd0 ι r) (u : Continuous r → _root_.UpperTheory.V.Z.Win.WitA ι r) : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r := ⟨h, u⟩
theorem autCsd0_of_isAutCsdA [IsCMField F] (h : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r) : AutCsd0 ι r := h.1
omit [NumberField F] in
theorem isAutomorphicOverImagQuad_of_isAutQA (h : _root_.UpperTheory.V.Z.Win.IsAutQA ι r) : IsAutomorphicOverImagQuad ι r := fun hc K _ _ _ _ _ _ h2 hi => (h hc K h2 hi).1
omit [NumberField F] in
theorem isAutQA_of_isAutomorphicOverImagQuad_of_witAQ (h : IsAutomorphicOverImagQuad ι r) (u : Continuous r → _root_.UpperTheory.V.Z.Win.WitAQ ι r) : _root_.UpperTheory.V.Z.Win.IsAutQA ι r :=
  fun hc K _ _ _ _ _ _ h2 hi => ⟨h hc K h2 hi, u hc K h2 hi⟩
end Conv
end UpperTheory.GalN.V
end
end
