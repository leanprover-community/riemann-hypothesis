module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtOfMulRight
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncModelFromLocalPatches
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem _root_.GlobalTheory.T.snc_model_from_local_patches : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ) (B : Set (Cpt ξ)) (bd : Ideal (MRing (fun _ : Unit => Fin (N + 1)))), (∀ c (p : Cpt ξ), Char0 ξ p → InChart ξ x c p → ∃ h ∈ Mdl.chartQ x c, unitAt ξ p h ∧ ∃ (z : Fin e → Mdl.invAdj (Mdl.chartQ x c) h) (n : ℕ), IsSncPatch (Pts ξ) (regAt ξ '' B) e (Mdl.invAdj (Mdl.chartQ x c) h) z n) → (∀ c, x c ≠ 0 → ∀ I : Ideal (Mdl.chartQ x c), I.IsPrime → ∃ p : Cpt ξ, Char0 ξ p ∧ InChart ξ x c p ∧ ∀ s : Mdl.chartQ x c, s ∉ I ↔ unitAt ξ p (s : Ω)) → (∀ c h, x c ≠ 0 → h ∈ Mdl.chartQ x c → h ≠ 0 → ∀ q : Ideal (Mdl.invAdj (Mdl.chartQ x c) h), q.IsPrime → ∃ p : Cpt ξ, Char0 ξ p ∧ InChart ξ x c p ∧ (∀ s : Mdl.invAdj (Mdl.chartQ x c) h, s ∉ q ↔ unitAt ξ p (s : Ω)) ∧ ∀ (z : Fin e → Mdl.invAdj (Mdl.chartQ x c) h) (n : ℕ), IsSncPatch (Pts ξ) (regAt ξ '' B) e (Mdl.invAdj (Mdl.chartQ x c) h) z n → (p ∈ B ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q)) → (∀ c (p : Cpt ξ), Char0 ξ p → InChart ξ x c p → (p ∈ B ↔ ∀ g ∈ bd, ¬ unitAt ξ p (Mdl.ratEval x c g))) → Cmp.IsSncModel (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) e bd := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.isSncModel_of_chart_patches | exact GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.isSncModel_of_chart_patches | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.isSncModel_of_chart_patches <;> assumption)
