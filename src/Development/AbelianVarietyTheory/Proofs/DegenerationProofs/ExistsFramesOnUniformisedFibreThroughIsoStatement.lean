module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormVal
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedFibreThroughIso
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

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_frames_on_uniformised_fibre_through_iso : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) → ∀ w : LB.Iso u.A.L (ρ.P.L.pull u.φ), w.IsGen → ∃ (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, FrAt (x a)), rig.IsGen ∧ GlobalTheory.ThetaPtMove.GenThrough w (fun _ : PUnit => eSec u.A.A) (fun _ : PUnit => eSec ρ.P.A) (fun _ => 1) rig ρ.rig (spMap u.yK) ∧ ∀ a, IsTorsFrame u.A rig (S.r * S.N) (x a) (e a) ∧ GlobalTheory.ThetaPtMove.GenThrough w (fun _ : Fin 1 => (x a).left) (fun _ : Fin 1 => (ρ.pt a).left) (fun _ => 1) (e a) (ρ.fr a) (spMap y₀) := by
  first | exact @GlobalTheory.exists_frames_on_fibre_through | exact GlobalTheory.exists_frames_on_fibre_through | (intros; apply GlobalTheory.exists_frames_on_fibre_through <;> assumption)
