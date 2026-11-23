module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLineBundleOfCompatibleLocalFrames
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.cech_lineBundle_of_compatible_local_frames : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (n : ℕ) (D : Fin (n + 1) → X.Opens), ⨆ i, D i = ⊤ → ∀ (τ : ∀ (i : Fin (n + 1)) (m : L.ι), Γ(X, D i ⊓ L.U m)ˣ), (∀ i x m m', x ∈ D i ⊓ L.U m → x ∈ D i ⊓ L.U m' → gm (𝟙 X) x _ (τ i m) = gm (𝟙 X) x _ (L.g m m') * gm (𝟙 X) x _ (τ i m')) → ∃ g : ∀ i j, Γ(X, D i ⊓ D j)ˣ, (⟨Fin (n + 1), D, g⟩ : LB X).IsLB ∧ LBIso L ⟨Fin (n + 1), D, g⟩ ∧ ∀ i j m, res (inf_le_left : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ D j) (g i j) = res (le_inf (inf_le_left.trans inf_le_right) inf_le_right : D i ⊓ D j ⊓ L.U m ≤ D j ⊓ L.U m) (τ j m) * (res (le_inf (inf_le_left.trans inf_le_left) inf_le_right : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ L.U m) (τ i m))⁻¹ := by
  first | exact @GlobalTheory.FramesBundle.frames_bundle | exact GlobalTheory.FramesBundle.frames_bundle | (intros; apply GlobalTheory.FramesBundle.frames_bundle <;> assumption)
