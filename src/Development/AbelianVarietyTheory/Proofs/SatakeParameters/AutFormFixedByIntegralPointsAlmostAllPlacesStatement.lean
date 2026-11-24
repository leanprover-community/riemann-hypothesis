module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOfNotApartOfNotSplit
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutFormFixedByIntegralPointsAlmostAllPlaces
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
open GlobalTheory.Cong.AdaptLev

theorem _root_.GlobalTheory.T.autForm_fixed_by_integralPoints_almostAllPlaces : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (φ : UA E a → ℂ), IsAutFormU φ → ∀ᶠ w in Filter.cofinite, ∀ x ∈ GlobalTheory.Cong.AdaptLev.intU a w, RU E a x φ = φ := by
  first | (exact @GlobalTheory.Cong.AutFormFix.fixed_intU_eventually) | (exact GlobalTheory.Cong.AutFormFix.fixed_intU_eventually) | (intros; apply GlobalTheory.Cong.AutFormFix.fixed_intU_eventually  <;> assumption)
