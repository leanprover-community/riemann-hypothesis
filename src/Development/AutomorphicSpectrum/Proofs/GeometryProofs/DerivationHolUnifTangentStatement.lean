module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecMapCompAppLE
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerivationHolUnifTangent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.InvDer
open scoped Topology

theorem _root_.GlobalTheory.T.derivation_hol_unif_tangent : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (A : Over (Sp ℂ)) [GrpObj A] (z : Sp ℂ ⟶ Sp R) (φ : A.left ⟶ G.left) (_ : IsGrpPullback A G z φ) (g : ℕ) (Lb : LB A.left) (u : HolUnif A Lb g) (v₀ : epsAt (𝟙 (Sp R)) ⟶ G) (hv₀ : IsTanAt G (𝟙 (Sp R)) v₀) (c : Fin g → ℂ) (v' : epsR ℂ ⟶ A), v'.left ≫ φ = spMap (dualMap (bmap z)) ≫ v₀.left → u.IsDiff c v' → ∀ (V : G.left.Opens) (hV : IsAffineOpen V) (f : Γ(G.left, V)) (w : Fin g → ℂ), ⊤ ≤ ((u.ex w).left ≫ φ) ⁻¹ᵁ V → fderiv ℂ (fun x => valAt' ((u.ex x).left ≫ φ) V f) w c = valAt' ((u.ex w).left ≫ φ) V (der v₀ hv₀ hV f) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.InvDer.fderiv_valAt_eq_der | exact GlobalTheory.CompanionTheory.Ar.InvDer.fderiv_valAt_eq_der | (intros; apply GlobalTheory.CompanionTheory.Ar.InvDer.fderiv_valAt_eq_der <;> assumption)
