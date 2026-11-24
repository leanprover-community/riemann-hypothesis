module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearChangeEulerProduct
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

open scoped CategoryTheory.Obj


theorem _root_.GlobalTheory.T.exists_dual_abelian_scheme : ∀ (Y : Scheme.{0}) (A G : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj G] [IsCommMonObj G] (χ : A ⟶ G) (P'' : LB (G2 G).left), IsAbelianScheme A → IsAbelianScheme G → IsMonHom χ → P''.IsLB → (∃ t : (P''.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P''.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → ∃ (D : Over Y) (_ : GrpObj D) (Q : LB (A ⊗ D).left) (h : A ⟶ D), IsAbelianScheme D ∧ GlobalTheory.AbDual.IsDual A D Q ∧ GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) ∧ IsMonHom h ∧ LBIso (P''.pull (χ ⊗ₘ χ).left) (Q.pull (lift (fst A A) (snd A A ≫ h)).left) := by
  first | (exact @GlobalTheory.DualHomPull.exists_dual_hom) | (exact GlobalTheory.DualHomPull.exists_dual_hom) | (intros; apply GlobalTheory.DualHomPull.exists_dual_hom  <;> assumption)
