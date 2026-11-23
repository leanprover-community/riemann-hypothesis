module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfIsDominant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionRatiosGenerateModMaximal
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_section_ratios_generate_mod_maximal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k : ℕ), k₀ ≤ k → ∀ (s₀ : H0 U.LG.L k) (i : Fin 1 → U.LG.L.ι) (w : (thickObj R (maximalIdeal R) e G).left), (fstG (maximalIdeal R) e G).left w ∈ secChart U.LG.L i → IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left w s₀ i) → ∃ (N : (thickObj R (maximalIdeal R) e G).left.Opens) (m : ℕ) (σ : Fin m → H0 U.LG.L k) (r : Fin m → Γ((thickObj R (maximalIdeal R) e G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y s₀ i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y (σ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y s₀ i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) e G).left, N), ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r Q - MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r P ∈ Ideal.map (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) (maximalIdeal R) := by
  first | exact @GlobalTheory.Mum.exists_ratio_gen_mod | exact GlobalTheory.Mum.exists_ratio_gen_mod | (intros; apply GlobalTheory.Mum.exists_ratio_gen_mod <;> assumption)
