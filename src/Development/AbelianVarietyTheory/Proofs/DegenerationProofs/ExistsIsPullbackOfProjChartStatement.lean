module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsHomOpenPart
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsPullbackOfProjChart
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

theorem _root_.GlobalTheory.T.exists_isPullback_of_projChart' : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') [IsNoetherianRing o] (N P : RatModel o Ω') (U₀ : M.Z.Opens) (b : N.Z ⟶ U₀.toScheme) (f : P.Z ⟶ M.Z) (J : Type) [Finite J] (t : J → Ω'), M.IsHom N φ (b ≫ U₀.ι) → M.IsHom P φ f → (∀ W : M.Z.Opens, W ≤ U₀ → IsAffineOpen W → (W : Set M.Z).Nonempty → M.ProjChart N φ (b ≫ U₀.ι) W t ∧ M.ProjChart P φ f W t) → ∃ a₀ : N.Z ⟶ P.Z, P.IsHom N (AlgHom.id o Ω') a₀ ∧ IsPullback a₀ b f U₀.ι := by
  first | exact @GlobalTheory.ZH.RatModel.exists_isPullback_of_projChart | exact GlobalTheory.ZH.RatModel.exists_isPullback_of_projChart | (intros; apply GlobalTheory.ZH.RatModel.exists_isPullback_of_projChart <;> assumption)
