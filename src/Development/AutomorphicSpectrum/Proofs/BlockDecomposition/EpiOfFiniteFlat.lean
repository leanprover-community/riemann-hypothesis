module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZarhinDualPolarisation.FlatFiniteFibres.FlatOfFibresFinite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.CompanionTheory.Dblock

theorem epiOfFF : PositivityTheory.Tls2.Zar3.Ch1.EpiOfFF := by
  intro R _ A B A' l hf hs hq g₁ g₂ h
  have : EffectiveEpi l.left := inferInstance
  have : Epi l.left := inferInstance
  apply Over.OverMorphism.ext
  rw [← cancel_epi l.left]
  simpa using congrArg (fun k => k.left) h

end GlobalTheory.CompanionTheory.Dblock
