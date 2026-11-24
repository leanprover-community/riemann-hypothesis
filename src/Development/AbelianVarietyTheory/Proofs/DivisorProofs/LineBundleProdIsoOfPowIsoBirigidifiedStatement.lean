module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleProdIsoOfPowIsoBirigidified
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor


theorem _root_.GlobalTheory.T.lineBundle_prod_iso_of_pow_iso_birigidified : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (k : ℕ) (P₁ P₂ : LB (G2 A).left), IsAbelianScheme A → 0 < k → IsUnit (k : Γ(S, ⊤)) → P₁.IsLB → (∃ t : (P₁.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P₁.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → P₂.IsLB → (∃ t : (P₂.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P₂.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso (lbPow P₁ k) (lbPow P₂ k) → LBIso P₁ P₂ := by
  first | (exact @GlobalTheory.BirigidRoot.iso_of_lbPow_iso) | (exact GlobalTheory.BirigidRoot.iso_of_lbPow_iso) | (intros; apply GlobalTheory.BirigidRoot.iso_of_lbPow_iso  <;> assumption)
