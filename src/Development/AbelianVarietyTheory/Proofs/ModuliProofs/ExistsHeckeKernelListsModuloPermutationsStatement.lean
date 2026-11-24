module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeKernelListsModuloPermutations
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

theorem _root_.GlobalTheory.T.exists_heckeKernelLists_modulo_permutations : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ), admitted l 𝔓 p → ∃ (Y Hk : Scheme.{0}) (q : Y ⟶ Hk) (π₁ : Hk ⟶ Xo.X) (oY : Ob D l ((q ≫ π₁) ≫ Xo.s)) (m : ObjMap oY Xo.univ (q ≫ π₁)) (σ : Fin n → (𝟙_ (Over Y) ⟶ oY.t.G)) (K : Set oY.t.G.left), IsFinite q ∧ Etale q ∧ Surjective q ∧ IsFinite π₁ ∧ Etale π₁ ∧ Lists (p ^ 2) σ K ∧ HeckeSet D oY.t 𝔓 p i K ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Y), y ≫ q = y' ≫ q ↔ Set.range (fun j => y ≫ (σ j).left ≫ m.toSABMap.φ) = Set.range (fun j => y' ≫ (σ j).left ≫ m.toSABMap.φ) ∧ y ≫ q ≫ π₁ = y' ≫ q ≫ π₁) ∧ ∀ (T : Scheme.{0}) (f : T ⟶ Xo.X) (t : SAB H T) (mu : SABMap t Xo.univ.t f) (τ : Fin n → (𝟙_ (Over T) ⟶ t.G)) (K' : Set t.G.left), Lists (p ^ 2) τ K' → HeckeSet D t 𝔓 p i K' → ∃ h : T ⟶ Y, h ≫ q ≫ π₁ = f ∧ ∀ j, h ≫ (σ j).left ≫ m.toSABMap.φ = (τ j).left ≫ mu.φ := by
  first | exact @GlobalTheory.HkPerm.exists_lists_mod_perm | exact GlobalTheory.HkPerm.exists_lists_mod_perm | (intros; apply GlobalTheory.HkPerm.exists_lists_mod_perm <;> assumption)
