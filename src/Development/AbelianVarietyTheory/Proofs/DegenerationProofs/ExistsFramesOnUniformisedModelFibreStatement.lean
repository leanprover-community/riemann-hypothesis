module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_frames_on_uniformisedModel_fibre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), ∀ x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) → ∃ (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, LB.Gen (LB.LinComb u.A.L (Y := (TFK (R := u.V) (PadicAlgCl p)).left) (K := Fin 1) (fun _ => (x a).left) (fun _ => 1))), rig.IsGen ∧ (∀ a, IsTorsFrame u.A rig (S.r * S.N) (x a) (e a)) ∧ ∀ (k : ℕ) (σ : LB.Sec (LPow ρ.P.A ρ.P.L (k : ℤ) (baseOver (Sp S.R)))), ∃ t : SecA u.A (PadicAlgCl p) k, ∀ (a : S.Gam) (c : S.R), IsValueAt ρ.P.A ρ.P.L (k : ℤ) σ (ρ.pt a) (powFrame ρ.P.A ρ.P.L (ρ.pt a) (ρ.fr a) (k : ℤ)) (fn c) → ∀ z J, Good u.A.L z J → sA t (ptSecT u.A.A (x a)).left z J = @id ((TFK (R := u.V) (PadicAlgCl p)).left.presheaf.stalk z) (cst (R := u.V) (PadicAlgCl p) z (y₀ c)) * (val (powFrame u.A.A u.A.L (x a) (e a) (k : ℤ)) (𝟙 _) z J).val := by
  first | exact @GlobalTheory.exists_frames_on_fibre | exact GlobalTheory.exists_frames_on_fibre | (intros; apply GlobalTheory.exists_frames_on_fibre <;> assumption)
