module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorMumfordBundleIsoOfGenerator
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveValueOfRingElementPsiRelation

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two


theorem _root_.GlobalTheory.T.exists_tensor_mumfordBundle_iso_of_generator : ∀ {S₀ S : Scheme.{0}} (B₀ : Over S₀) [GrpObj B₀] [IsCommMonObj B₀] (B : Over S) [GrpObj B] [IsCommMonObj B] (L₀ : LB B₀.left) (M : LB B.left), L₀.IsLB → M.IsLB → ∀ (β₂ : (G2 B₀).left ⟶ (G2 B).left) (wR : LB.Iso (abelian₂ B₀ L₀) ((abelian₂ B M).pull β₂)), wR.IsGen → ∀ {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (Y : Over S₀) (x : Fin r → (Y ⟶ B₀)) (φ : (Fin r × Fin r) × Fin 4 → (Y.left ⟶ B.left)) (ε : (Fin r × Fin r) × Fin 4 → ℤ), (∀ k, φ k = (lift (x k.1.1) (x k.1.2)).left ≫ β₂ ≫ (psum B (x2 B) ((![{0, 1}, {0}, {1}, ∅] : Fin 4 → Finset (Fin 2)) k.2)).left) → (∀ k, ε k = W k.1.1 k.1.2 * Oε k.2) → ∃ v : LB.Iso (LB.LinComb L₀ (tensφ x) (tensε W)) ((LB.LinComb M φ ε).pull (𝟙 Y.left)), v.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y.left) (z : Z) (J : (Z ⟶ B.left) → M.ι) (J₀ : (Z ⟶ B₀.left) → L₀.ι), Good M z J → Good L₀ z J₀ → GlobalTheory.Mum.Two.isoVal v q z J J₀ = ∏ a, ∏ b, lamVal wR (q ≫ (lift (x a) (x b)).left) z J J₀ ^ W a b := by
  first | exact @GlobalTheory.Mum.LamBridge.exists_iso_tens | exact GlobalTheory.Mum.LamBridge.exists_iso_tens | (intros; apply GlobalTheory.Mum.LamBridge.exists_iso_tens <;> assumption)
