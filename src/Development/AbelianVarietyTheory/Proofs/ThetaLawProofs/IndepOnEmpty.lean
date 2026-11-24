module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.RelBasis

variable {X Y T : Scheme.{0}} {L : LB X} {t : ℤ} {N : ℕ}

def comb (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) (W : T.Opens) (c : Fin N → Γ(T, W)) (y : Y)
    (i : L.ι) : Y.presheaf.stalk y :=
  ∑ k, gs p₁ y W (c k) * gs p₂ y (L.U i) ((b k).f i)

def IndepOn (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) (W : T.Opens) : Prop :=
  ∀ c : Fin N → Γ(T, W), (∀ (y : Y) (i : L.ι), p₁ y ∈ W → p₂ y ∈ L.U i → comb b p₁ p₂ W c y i = 0) → c = 0

def SpanOn (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) (W : T.Opens) : Prop :=
  ∀ σ : ∀ i : L.ι, Γ(Y, p₁ ⁻¹ᵁ W ⊓ p₂ ⁻¹ᵁ L.U i),
    (∀ (y : Y) (i i' : L.ι), p₁ y ∈ W → p₂ y ∈ L.U i → p₂ y ∈ L.U i' →
      gs (𝟙 Y) y _ (σ i) = (gm p₂ y (L.U i ⊓ L.U i') (L.g i i') ^ t).val * gs (𝟙 Y) y _ (σ i')) →
    ∃ c : Fin N → Γ(T, W), ∀ (y : Y) (i : L.ι), p₁ y ∈ W → p₂ y ∈ L.U i →
      gs (𝟙 Y) y _ (σ i) = comb b p₁ p₂ W c y i

def BoxSpan (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) : Prop :=
  ∀ (K : Type) [Fintype K] (φ : K → (T ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L (K := K ⊕ PUnit) (Sum.elim (fun k => p₁ ≫ φ k) (fun _ => p₂)) (Sum.elim ε (fun _ => t)))),
    ∃ a : Fin N → LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval s r z J = ∑ k, sval (a k) (r ≫ p₁) z J * gs (r ≫ p₂) z (L.U (J (r ≫ p₂))) ((b k).f (J (r ≫ p₂)))

theorem gs_comp {Z : Scheme.{0}} (r : Z ⟶ Y) (f : Y ⟶ X) (z : Z) (U : X.Opens) (h : f (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ f) z U a = (r.stalkMap z).hom (gs f (r z) U a) := by
  rw [← gs_pull r f z U h, gs_eq f (r z) U h, gs_eq r z (f ⁻¹ᵁ U) h]
  exact (Scheme.Hom.germ_stalkMap_apply r (f ⁻¹ᵁ U) z h _).symm

def gsHom (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) : Γ(X, U) →+* Y.presheaf.stalk y :=
  (Y.presheaf.germ (f ⁻¹ᵁ U) y h).hom.comp (f.app U).hom

theorem gs_eq_gsHom (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) :
    gs f y U a = gsHom f y U h a := gs_eq f y U h a

theorem comb_comp {Z : Scheme.{0}} (b : Fin N → LB.Sec (pw L t)) (r : Z ⟶ Y) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) (W : T.Opens)
    (c : Fin N → Γ(T, W)) (z : Z) (i : L.ι) (h₁ : p₁ (r z) ∈ W) (h₂ : p₂ (r z) ∈ L.U i) :
    comb b (r ≫ p₁) (r ≫ p₂) W c z i = (r.stalkMap z).hom (comb b p₁ p₂ W c (r z) i) := by

  rw [comb, comb, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, gs_comp r p₁ z W h₁]
  exact congrArg _ (gs_comp r p₂ z (L.U i) h₂ _)

end GlobalTheory.RelBasis
