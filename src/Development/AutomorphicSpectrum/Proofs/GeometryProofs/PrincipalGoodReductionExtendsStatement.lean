module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalGoodReductionExtends
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar


theorem _root_.GlobalTheory.T.principal_good_reduction_extends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t : SAB H (Sp L)), IsPrincipal t → (∀ (σ : L →+* ℂ) (τ : 𝓞 E →+* ℂ), LieMult t.act (spMap σ) τ 0) → ∃ t' : SAB H (Sp (𝓞 L)), Nonempty (SABMap t t' (spMap (algebraMap (𝓞 L) L))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TrivialModel.exists_model_of_rank_zero | exact GlobalTheory.CompanionTheory.Ar.TrivialModel.exists_model_of_rank_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.TrivialModel.exists_model_of_rank_zero <;> assumption)
