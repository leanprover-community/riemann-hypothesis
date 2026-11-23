module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPointsTransferDominating
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.snc_points_transfer_dominating : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ₁ κ₂ : Type) (x₁ : κ₁ → Ω) (x₂ : κ₂ → Ω) (X₁ X₂ : Scheme.{0}) (ξ₁ : Sp Ω ⟶ X₁) (ξ₂ : Sp Ω ⟶ X₂) (g : X₂ ⟶ X₁) (e : ℕ) (Ab : Set X₁), (∀ q : X₁, genPt ξ₁ ⤳ q) → (∀ q : X₂, genPt ξ₂ ⤳ q) → CoordTie ℤ ξ₁ x₁ → CoordTie ℤ ξ₂ x₂ → GlobalTheory.CompanionTheory.Ar.Dominates ξ₂ ξ₁ g (RingHom.id Ω) → (∀ q ∈ genFib ξ₁, IsoAt ξ₂ g (RingHom.id Ω) q) → SncPts ξ₁ e {p | Char0 ξ₁ p ∧ p.1 ∉ Ab} → SncPts ξ₂ e {p | Char0 ξ₂ p ∧ g p.1 ∉ Ab} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PatchIso.sncPts_of_isoAt | exact GlobalTheory.CompanionTheory.Ar.PatchIso.sncPts_of_isoAt | (intros; apply GlobalTheory.CompanionTheory.Ar.PatchIso.sncPts_of_isoAt <;> assumption)
