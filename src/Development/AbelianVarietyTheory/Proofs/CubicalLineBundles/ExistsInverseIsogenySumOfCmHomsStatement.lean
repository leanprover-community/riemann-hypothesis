module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsInverseIsogenySumOfCmHoms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF


theorem _root_.GlobalTheory.T.exists_inverse_isogeny_sum_of_cm_homs : ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (A A' B : Out.PolAV (Sp (𝓞 K))) (p q : ℕ) (φ : Fin p → (A.A ⟶ B.A)) (φ' : Fin q → (A'.A ⟶ B.A)), (∀ i, IsMonHom (φ i)) → (∀ i, IsMonHom (φ' i)) → B.g = p * A.g + q * A'.g → (∀ y : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ B.A, ∃ (x : Fin p → (Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.A)) (x' : Fin q → (Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A'.A)), y = (List.ofFn fun i => x i ≫ φ i).prod * (List.ofFn fun i => x' i ≫ φ' i).prod) → ∃ (N : ℕ) (ψ : Fin p → (B.A ⟶ A.A)) (ψ' : Fin q → (B.A ⟶ A'.A)), 0 < N ∧ (∀ (Tb : Over (Sp (𝓞 K))) (x : Tb ⟶ B.A), padd B.A (psumPt fun i => x ≫ ψ i ≫ φ i) (psumPt fun i => x ≫ ψ' i ≫ φ' i) = pnsmulPt N x) ∧ ∀ (Tb : Over (Sp (𝓞 K))) (a : Fin p → (Tb ⟶ A.A)) (a' : Fin q → (Tb ⟶ A'.A)), (∀ i, padd B.A (psumPt fun k => a k ≫ φ k) (psumPt fun k => a' k ≫ φ' k) ≫ ψ i = pnsmulPt N (a i)) ∧ ∀ i, padd B.A (psumPt fun k => a k ≫ φ k) (psumPt fun k => a' k ≫ φ' k) ≫ ψ' i = pnsmulPt N (a' i) := by
  first | exact @GlobalTheory.LamF.exists_inverse_isogeny_of_sum | exact GlobalTheory.LamF.exists_inverse_isogeny_of_sum | (intros; apply GlobalTheory.LamF.exists_inverse_isogeny_of_sum <;> assumption)
