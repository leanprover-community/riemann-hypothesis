module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.AmplePlusNefInduction
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
theorem _root_.GlobalTheory.T.ample_plus_nef_induction : ∀ (k : Type) [Field k] [Infinite k] (d : ℕ), (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k (X := Y)) → topologicalKrullDim Y ≤ (d : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) → (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k (X := Y)) → topologicalKrullDim Y ≤ (d + 1 : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) := by
  first | exact @_root_.GlobalTheory.isAmpleLB_tens_of_isNef_succ | exact _root_.GlobalTheory.isAmpleLB_tens_of_isNef_succ | (intros; apply _root_.GlobalTheory.isAmpleLB_tens_of_isNef_succ <;> assumption)
