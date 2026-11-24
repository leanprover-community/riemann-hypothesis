module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsIsoRestrictOfBlowupComp
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

theorem _root_.GlobalTheory.T.isIso_restrict_of_blowup_comp : ∀ {X X₁ X₂ : Scheme.{0}} (s : X₁ ⟶ X) (π : X₂ ⟶ X₁) (Z : X₁.IdealSheafData) (V : X.Opens), IsIntegral X₁ → IsSeparated s → FinalTheorems.Blowup π Z → Nonempty X₂ → IsIso ((π ≫ s) ∣_ V) → IsIso (s ∣_ V) ∧ IsIso (π ∣_ (s ⁻¹ᵁ V)) := by
  first | exact @GlobalTheory.CompanionTheory.Principalise.isIso_restrict_of_isIso_restrict_comp_blowup | exact GlobalTheory.CompanionTheory.Principalise.isIso_restrict_of_isIso_restrict_comp_blowup | (intros; apply GlobalTheory.CompanionTheory.Principalise.isIso_restrict_of_isIso_restrict_comp_blowup <;> assumption)
