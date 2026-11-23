module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GermDerivationIffDualNumberPoint
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
theorem _root_.GlobalTheory.T.germDerivation_iff_dualNumberPoint : ∀ (X : Scheme.{0}) (y : Sp ℂ ⟶ X), (∀ δ, PtDer y δ → ∃! v : Sp (DualNumber ℂ) ⟶ X, (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ v = y ∧ ∀ (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)), TrivSqZeroExt.snd (show DualNumber ℂ from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.appLE W ⊤ h).hom f)) = δ W f) ∧ ∀ v : Sp (DualNumber ℂ) ⟶ X, (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ v = y → ∃ δ, PtDer y δ ∧ ∀ (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)), TrivSqZeroExt.snd (show DualNumber ℂ from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.appLE W ⊤ h).hom f)) = δ W f := by
  first | exact @GlobalTheory.KS.ptDer_iff_dualPoint | exact GlobalTheory.KS.ptDer_iff_dualPoint | (intros; apply GlobalTheory.KS.ptDer_iff_dualPoint <;> assumption)
