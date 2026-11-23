module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtLIPreimageMono
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LePreimageOfCompEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumMulPulledBackFunctionsGenericFibreEq
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.sum_mul_pulledBack_functions_genericFibre_eq : ∀ {X Y S S' T X' : Scheme.{0}} (g : X ⟶ S) (h : S' ⟶ S) (gp : T ⟶ S) (gp' : T ⟶ S') (hgp : gp' ≫ h = gp) (fst : X' ⟶ X) (snd : X' ⟶ S'), fst ≫ g = snd ≫ h → ∀ (α : Y ⟶ X) (t : Y ⟶ T) (hpb : α ≫ g = t ≫ gp) (l : Y ⟶ X') (h1 : l ≫ fst = α), l ≫ snd = t ≫ gp' → ∀ (W : X.Opens) (U : S.Opens) (hWU : W ≤ g ⁻¹ᵁ U) (n : ℕ) (c : Fin n → Γ(X, W)) (b : Fin n → Γ(T, gp ⁻¹ᵁ U)) (b' : Fin n → Γ(S', h ⁻¹ᵁ U)), (∀ m, (gp'.appLE (h ⁻¹ᵁ U) (gp ⁻¹ᵁ U) (le_preimage_of_comp_eq gp gp' h hgp U)).hom (b' m) = b m) → ∃ y : Γ(X', fst ⁻¹ᵁ W), (l.app (fst ⁻¹ᵁ W)).hom y = (Y.presheaf.map (homOfLE (extLI_preimage_le l fst α h1 W)).op).hom (∑ m, (α.app W).hom (c m) * (t.appLE (gp ⁻¹ᵁ U) (α ⁻¹ᵁ W) (locInt_le_gen g α t gp hpb W U hWU)).hom (b m)) := by
  first | exact @GlobalTheory.Mum.exists_app_eq_sum_mul_of_comm | exact GlobalTheory.Mum.exists_app_eq_sum_mul_of_comm | (intros; apply GlobalTheory.Mum.exists_app_eq_sum_mul_of_comm <;> assumption)
