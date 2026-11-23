module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CechDeRhamCoefMapOneFormsRestrictAlongFunctor
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestSide
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftSemiBijectiveOfExactCokernel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalOneCochainsBaseChangeBijectiveFiniteCategorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalTwoCochainsFiniteCategoryBaseChangeBijectivStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalZeroCochainsFiniteCategoryBaseChangeBijectiStatement
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem liftSemi_pullHyp1_bijective_of_finite : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → Function.Bijective (liftSemi (pullHyp1 (⟨𝟭 C, α, hn, hs⟩ : CoefMap (algebraMap R R') F F'))) := by
  intro R R' _ _ _ _ C _ _ _ F F' α hn hs hb
  let m : CoefMap (algebraMap R R') F F' := ⟨𝟭 C, α, hn, hs⟩
  let g : Tot0 F →ₛₗ[algebraMap R R'] Tot0 F' :=
    { toFun := fun x T ↦ α T (x T)
      map_add' := fun x y ↦ funext fun T ↦ map_add (α T) (x T) (y T)
      map_smul' := fun r x ↦ funext fun T ↦ hs T r (x T) }
  have h0 : Function.Bijective (liftSemi g) :=
    GlobalTheory.T.bijective_liftSemi_tot0_of_bijective R R' C F F' α hn hs hb g fun _ _ ↦ rfl
  have h1 : Function.Bijective (liftSemi (pullTot1 m)) := GlobalTheory.T.totalOneCochains_baseChange_bijective_finiteCategory R R' C F F' α hn hs hb
  have h2 : Function.Bijective (liftSemi (pullTot2 m)) := GlobalTheory.T.totalTwoCochains_finiteCategory_baseChange_bijective R R' C F F' α hn hs hb
  have hZ : Function.Bijective (liftSemi (pullZZ1 m)) :=
    GlobalTheory.KerFlat.main R R' (cechDeRhamTotalCocyclesOne F) (Tot1 F) (Tot2 F) (cechDeRhamTotalCocyclesOne F') (Tot1 F') (Tot2 F')
      (cechDeRhamTotalCocyclesOne F).subtype (dTot1 F) (cechDeRhamTotalCocyclesOne F').subtype (dTot1 F') (pullZZ1 m) (pullTot1 m) (pullTot2 m)
      (cechDeRhamTotalCocyclesOne F).injective_subtype (LinearMap.exact_subtype_ker_map (dTot1 F))
      (cechDeRhamTotalCocyclesOne F').injective_subtype (LinearMap.exact_subtype_ker_map (dTot1 F'))
      (fun _ ↦ rfl) (fun x ↦ (pullTot2_dTot1 m x).symm) h1 h2.1
  exact GlobalTheory.liftSemi_bijective_of_exact_cokernel R R' (Tot0 F) (cechDeRhamTotalCocyclesOne F) (Hyp1 F) (Tot0 F') (cechDeRhamTotalCocyclesOne F') (Hyp1 F')
    ((dTot0 F).codRestrict (cechDeRhamTotalCocyclesOne F) (dTot0_mem F)) (Hyp1.mk F)
    ((dTot0 F').codRestrict (cechDeRhamTotalCocyclesOne F') (dTot0_mem F')) (Hyp1.mk F') g (pullZZ1 m) (pullHyp1 m)
    (LinearMap.exact_map_mkQ_range _) (Hyp1.mk_surjective F)
    (LinearMap.exact_map_mkQ_range _) (Hyp1.mk_surjective F')
    (fun x ↦ Subtype.ext (pullTot1_dTot0 m x).symm) (fun z ↦ (pullHyp1_mk m z).symm) h0.2 hZ

end GlobalTheory
