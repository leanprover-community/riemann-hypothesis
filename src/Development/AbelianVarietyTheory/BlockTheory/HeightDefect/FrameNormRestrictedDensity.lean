module

public import Formalism.LocalToGlobal.ProjectiveLattices.CompOrd
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FrameNormRestrictedDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7} {T : Core D}

abbrev FrameNorms (T : Core D) (j : ℕ) : Type :=
  ∀ σ : T.Q.c.F →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt σ) → Ix (T.Q.Dw j) → ℝ

abbrev GenericFrames (T : Core D) (j : ℕ) : Type :=
  ∀ Z : Comp (T.Q.Xo j) T.Q.c, ∀ P : Om Z →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt (sgOf P))

end GlobalTheory.IndefiniteRowSideFullHecke.FrameNormRestrictedDensity
