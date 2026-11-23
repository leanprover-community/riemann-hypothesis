module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleIsoOfAmpleDeterminantFrames
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem _root_.GlobalTheory.T.lineBundleIso_of_ampleDeterminantFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z Z₁ Z₂ : Scheme.{0}) [IsLocallyNoetherian Z] (z : Z ⟶ Sp ℤ) (t : SAB H Z) (t₁ : SAB H Z₁) (t₂ : SAB H Z₂) (f₁ : Z ⟶ Z₁) (f₂ : Z ⟶ Z₂) (_ : SABMap t t₁ f₁) (_ : SABMap t t₂ f₂) (N : ℕ) (A₁ : GlobalTheory.LN.AmpFrames t₁.G t₁.PP.L N) (A₂ : GlobalTheory.LN.AmpFrames t₂.G t₂.PP.L N), IsNormalScheme Z → Flat z → genericPoints Z ⊆ abLocus t.G → A₁.r = A₂.r → A₁.s = A₂.s → LBIso (A₁.A.pull f₁) (A₂.A.pull f₂) := by
  first | exact @GlobalTheory.FrameCmp.lbIso_of_ampFrames | exact GlobalTheory.FrameCmp.lbIso_of_ampFrames | (intros; apply GlobalTheory.FrameCmp.lbIso_of_ampFrames <;> assumption)
