module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorTranslateRatioGlobalUnit
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT.Hecke.PullInj

theorem _root_.GlobalTheory.T.generator_translate_ratio_global_unit : ∀ (X X' : Scheme.{0}) (π : X ⟶ X') (Q₁ Q₂ : LB X'), Q₁.IsLB → Q₂.IsLB → ∀ (w : LB.Iso (Q₁.pull π) (Q₂.pull π)), w.IsGen → ∀ τ : X ⟶ X, τ ≫ π = π → ∃ f : Γ(X, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (k : (PUnit → Q₂.ι) × (PUnit → Q₁.ι)), r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k → gm (r ≫ τ) z _ (w.s k) = gm r z ⊤ f * gm r z _ (w.s k) := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.PullInj.gen_transl_ratio) | (exact GlobalTheory.UPel.HT.Hecke.PullInj.gen_transl_ratio) | (intros; apply GlobalTheory.UPel.HT.Hecke.PullInj.gen_transl_ratio  <;> assumption)
