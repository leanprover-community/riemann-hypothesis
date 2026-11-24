module

public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.DedekindFactorK
public import Mathlib.RingTheory.FractionalIdeal.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise

def mmR {E : Type} [Field E] [NumberField E] (M : IntermediateField ℚ ℂ) [NumberField M] {ι : Type}
    (emb : ι → E →+* ℂ) (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 M) (ι → M) :=
  Submodule.span (𝓞 M) {v | ∃ a ∈ (I : Submodule (𝓞 E) E), v = fun i => liftM M (emb i a)}

def lineR {E : Type} [Field E] [NumberField E] (M : IntermediateField ℚ ℂ) [NumberField M] {ι : Type}
    [DecidableEq ι] (emb : ι → E →+* ℂ) (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (i : ι) : Submodule (𝓞 M) M :=
  (mmR M emb I).comap (LinearMap.single (𝓞 M) (fun _ : ι => (M : Type)) i)

def imI {E : Type} [Field E] [NumberField E] (M : IntermediateField ℚ ℂ) [NumberField M]
    (σ : E →+* ℂ) (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 M) M :=
  Submodule.span (𝓞 M) {y | ∃ a ∈ (J : Submodule (𝓞 E) E), y = liftM M (σ a)}

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
