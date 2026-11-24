module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTermsDividingLabelGroupMember
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep


theorem _root_.GlobalTheory.T.exists_terms_dividing_label_group_member : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (m1 : ℕ) (t1 : Fin m1 → V1) (δ1 : Fin m1 → LinearMap.BilinForm ℤ Y1) (𝔪1 : UMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (a : X₁.S.Gam), a ∈ X₁.S.HH X₁.M z₁ → ∃ T : (Fin 8 → Y1) → Unit → V1, 𝔪1.Terms x₀ (fun _ : Unit => a) T := by
  first | exact @GlobalTheory.Poinc.Sep.exists_terms_single | exact GlobalTheory.Poinc.Sep.exists_terms_single | (intros; apply GlobalTheory.Poinc.Sep.exists_terms_single <;> assumption)
