module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensHomTmul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs.BC

theorem natCoef_pull1_bijective (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F F' : C ⥤ CommAlgCat.{0} R)
    (α : ∀ T, F.obj T →+* F'.obj T)
    (nat : ∀ {T T' : C} (a : T ⟶ T') (b : F.obj T), α T' (mp F a b) = mp F' a (α T b))
    (smul : ∀ T (r : R) (b : F.obj T), α T (r • b) = r • α T b) :
    (∀ T, Function.Bijective (α T)) → Function.Bijective (GlobalTheory.Obs.BC.natCoef α nat smul).pull1 := by
  intro hb
  let β : ∀ T, F'.obj T →+* F.obj T := fun T ↦ (RingEquiv.ofBijective (α T) (hb T)).symm.toRingHom
  have hαβ : ∀ T (b : F'.obj T), α T (β T b) = b := fun T b ↦
    (RingEquiv.ofBijective (α T) (hb T)).apply_symm_apply b
  have hβα : ∀ T (b : F.obj T), β T (α T b) = b := fun T b ↦
    (RingEquiv.ofBijective (α T) (hb T)).symm_apply_apply b
  have natβ : ∀ {T T' : C} (a : T ⟶ T') (b : F'.obj T), β T' (mp F' a b) = mp F a (β T b) := by
    intro T T' a b
    apply (hb T').1
    rw [hαβ, nat, hαβ]
  have smulβ : ∀ T (r : R) (b : F'.obj T), β T (r • b) = r • β T b := by
    intro T r b
    apply (hb T).1
    rw [hαβ, smul, hαβ]
  let m := GlobalTheory.Obs.BC.natCoef α nat smul
  let n := GlobalTheory.Obs.BC.natCoef β natβ smulβ
  have left : ∀ c, n.pull1 (m.pull1 c) = c := by
    intro c
    obtain ⟨f, rfl⟩ := H1.mk_surjective F c
    rw [CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class]
    congr 1
    refine Subtype.ext ?_
    funext T T' φ
    exact hβα T' _
  have right : ∀ c, m.pull1 (n.pull1 c) = c := by
    intro c
    obtain ⟨f, rfl⟩ := H1.mk_surjective F' c
    rw [CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class]
    congr 1
    refine Subtype.ext ?_
    funext T T' φ
    exact hαβ T' _
  exact ⟨Function.LeftInverse.injective left, Function.RightInverse.surjective right⟩

end GlobalTheory.Obs.BC
