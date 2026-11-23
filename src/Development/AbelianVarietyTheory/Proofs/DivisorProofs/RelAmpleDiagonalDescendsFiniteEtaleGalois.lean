module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalExtendedBundleOfGeneric
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleKTrivOfFiniteEtaleCover
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.DescGal

theorem relAmple_diag_descends : ∀ (X Y : Scheme.{0}) [IsLocallyNoetherian Y] (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → Out.RelAmple A₀ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) := by
  intro X Y _ π Ga _ ρ A _ _ A₀ _ _ φ φ₂ P P₀ hπ _ hA₀ gp sq hP hP₀ hw hamp
  have hc : (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ = φ ≫ (lift (𝟙 A₀) (𝟙 A₀)).left :=
    (GlobalTheory.DiagAmpleExt.diag_comm φ φ₂ sq).symm
  have H₁ : LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left) ((P₀.pull φ₂).pull (lift (𝟙 A) (𝟙 A)).left) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull P _ _ rfl)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (P₀.pull φ₂) _ _ rfl) hw
  have H₂ : LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left) (P₀.pull ((lift (𝟙 A) (𝟙 A)).left ≫ φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn P₀ (fun _ : PUnit => φ₂) (fun _ => 1) _) H₁
  have H₃ : LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left) ((P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left).pull φ) :=
    LBIso.chartPull (chartPullId _)
      (chartPullOut P₀ (fun _ : PUnit => (lift (𝟙 A₀) (𝟙 A₀)).left) (fun _ => 1) φ
        (fun _ => (lift (𝟙 A) (𝟙 A)).left ≫ φ₂) fun _ => hc) H₂
  exact (GlobalTheory.relAmple_kTriv_of_finite_etale_cover Y X π A₀ A φ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left)
    (P.pull (lift (𝟙 A) (𝟙 A)).left) hπ.fin hπ.etale hπ.onto hA₀ (pull_isLB hP₀ _) (pull_isLB hP _) gp H₃).1 hamp

end GlobalTheory.DescGal
