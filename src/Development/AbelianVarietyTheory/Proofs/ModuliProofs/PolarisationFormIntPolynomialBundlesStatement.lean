module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarisationFormIntPolynomialBundles
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

theorem _root_.GlobalTheory.T.polarisationForm_intPolynomial_bundles : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (s : P.A ⟶ P.A), M.IsLB → FormIs P M s → (∃ ev : Polynomial ℤ → (P.A ⟶ P.A), ev 1 = 𝟙 P.A ∧ (∀ F G, ev (F + G) = ev F * ev G) ∧ ∀ F, ev (Polynomial.X * F) = ev F ≫ s) ∧ ∀ (ev : Polynomial ℤ → (P.A ⟶ P.A)), ev 1 = 𝟙 P.A → (∀ F G, ev (F + G) = ev F * ev G) → (∀ F, ev (Polynomial.X * F) = ev F ≫ s) → (∀ F, IsMonHom (ev F)) ∧ (∀ F G, ev (F * G) = ev F ≫ ev G) ∧ (∀ F, FormIs P (cubeLB P.A ![𝟙 P.A, ev (F)] P.L) (ev (2 * F))) ∧ (∀ F G, LBIso (cubeLB P.A ![𝟙 P.A, ev (G ^ 2 * F)] P.L) ((cubeLB P.A ![𝟙 P.A, ev (F)] P.L).pull (ev G).left)) ∧ (∀ F G, LBIso (LB.div (cubeLB P.A ![𝟙 P.A, ev (F + G)] P.L) (cubeLB P.A ![𝟙 P.A, ev (F)] P.L)) (cubeLB P.A ![𝟙 P.A, ev (G)] P.L)) ∧ LBIso (cubeLB P.A ![𝟙 P.A, ev (1)] P.L) (lbPow P.L 2) ∧ (SymB M → LBIso (cubeLB P.A ![𝟙 P.A, ev (Polynomial.X)] P.L) (lbPow M 2)) := by
  first | exact @GlobalTheory.formPoly_bundles | exact GlobalTheory.formPoly_bundles | (intros; apply GlobalTheory.formPoly_bundles <;> assumption)
