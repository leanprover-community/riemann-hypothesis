module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianFieldPointEqEighthPowerUniversalPullb
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical


theorem _root_.GlobalTheory.T.semiAbelian_fieldPoint_eq_eighthPower_universal_pullback : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ (K : Type) [Field K] (t : Sp K ⟶ V.toScheme) (B : Over (Sp K)) [GrpObj B] (φB : B.left ⟶ FinalForm.G.left), IsGrpPullback B FinalForm.G (t ≫ V.ι) φB → ∃ (c' : SiegPre g n ζ ((t ≫ v) ≫ F.s)) (pr' : Fin 8 → (B ⟶ c'.A)), SiegPB c' F.univ (t ≫ v) ∧ (∀ a, IsMonHom (pr' a)) ∧ (∀ (T' : Over (Sp K)) (y : Fin 8 → (T' ⟶ c'.A)), ∃! x : T' ⟶ B, ∀ a, x ≫ pr' a = y a) ∧ (∀ L' : LB B.left, L'.IsLB → LBIso L' (FinalForm.L.L.pull φB) → LBIso L' (LB.LinComb c'.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => W ab.1 ab.2))) ∧ ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G) (fB : B ⟶ B), MatOn FinalForm pr a b f → fB.left ≫ φB = φB ≫ f.left → MatEnd pr' a b fB := by
  first | exact @GlobalTheory.Poinc.Eq8.FieldPt.main | exact GlobalTheory.Poinc.Eq8.FieldPt.main | (intros; apply GlobalTheory.Poinc.Eq8.FieldPt.main <;> assumption)
