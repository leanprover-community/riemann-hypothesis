module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtPull

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

theorem symLift_thTw : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (τ : Kb R →ₐ[FractionRing R] Kb R) (x x' : TFK (R := R) (Kb R) ⟶ A.A) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) (Kb R))), SymLift A.A A.L N N x θ → x'.left = spMap τ.toRingHom ≫ x.left → SymLift A.A A.L N N x' (thTw A N τ θ) := by
  intro R _ _ A N τ x x' θ h hx
  have ex : x' = twK τ ≫ x := Over.OverMorphism.ext (by rw [hx, Over.comp_left, twK_left])
  subst ex
  have eM : mTw A τ = twK τ ▷ A.A := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [mTw_fst, whiskerRight_fst]
    · rw [mTw_snd, whiskerRight_snd]
  exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.symLift_pull A.isLB (twK τ) h _ (thTw A N τ θ).isGen fun r z J hJ => by
    show val (genCast _ _) r z J = _
    rw [val_genCast]
    exact (val_pull hJ _ _ r).trans (by rw [eM])

end GlobalTheory.Mum.Conj
