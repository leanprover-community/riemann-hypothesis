module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RatTors
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsomorphismValuesCocycleEqBundleIsoValue
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

theorem _root_.GlobalTheory.T.isomorphismValues_cocycle_eq_bundleIso_value : Laws → Laws2 → ∀ (R O' : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing O'] [IsDomain O'] [IsNoetherianRing O'] (f : O' →+* R) (P : DegPre R) (D₀ : DegPre O') (C : Type) [Field C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing R) C] [Algebra (FractionRing O') C], Along f C → ∀ (N' N : NumD C) (ν' : NumOf P C N') (ν : NumOf D₀ C N) (ψ : P.P.A.left ⟶ D₀.P.A.left) (w : LB.Iso P.P.L (D₀.P.L.pull ψ)) (I : NumB.Iso N.toNumB N'.toNumB), IsGrpPullback P.P.A D₀.P.A (spMap f) ψ → w.IsGen → (∀ x : N.A, (ν'.eA (I.φ x)).left ≫ ψ = (ν.eA x).left) → (∀ x, wVal ν' ν w x ≠ 0) ∧ ∀ x : N.A, (I.h x : C) * wVal ν' ν w (I.φ x) = wVal ν' ν w 1 := by
  first | exact @GlobalTheory.IsoValCocycle.cocycle_eq_val | exact GlobalTheory.IsoValCocycle.cocycle_eq_val | (intros; apply GlobalTheory.IsoValCocycle.cocycle_eq_val <;> assumption)
