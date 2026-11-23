module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
open GlobalTheory.LieVB GlobalTheory.Conormal

namespace GlobalTheory.SqZeroPt

theorem zeroSec_sqZeroMap (O : Type) [CommRing O] (M N : Type) [AddCommGroup M] [Module O M]
    [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N]
    [IsCentralScalar O N] (l : M →ₗ[O] N) :
    zeroSec O N ≫ GlobalTheory.GrpTangent.sqZeroMap l = zeroSec O M := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  simp

theorem Phi_sqZeroMap_comp : ∀ (O : Type) [CommRing O] (M N : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N] [IsCentralScalar O N] (A : Over (Sp O)) [GrpObj A] (l : M →ₗ[O] N) (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O N ≫ (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) = η[A]) (w : Wmod A), Phi (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) h' w = l (Phi z h w) := by
  intro O _ M N _ _ _ _ _ _ _ _ A _ l z h h' w
  have hl := zeroSec_sqZeroMap O M N l
  rw [Phi_apply, Phi_apply, ← cotMap_comp h hl rfl h']
  obtain ⟨b, hb⟩ := (isChart O M).d_surjective (sec_hom (zeroSec O M)) ((cotMap z h).app ⊤ w)
  have e : (ConcreteCategory.hom (Scheme.Modules.Hom.app (cotMap z h ≫ cotMap (GlobalTheory.GrpTangent.sqZeroMap l) hl) ⊤)) w = (ConcreteCategory.hom (Scheme.Modules.Hom.app (cotMap (GlobalTheory.GrpTangent.sqZeroMap l) hl) ⊤)) ((ConcreteCategory.hom (Scheme.Modules.Hom.app (cotMap z h) ⊤)) w) := rfl
  rw [e, ← hb, cotMap_d (GlobalTheory.GrpTangent.sqZeroMap l) hl _ (le_preimage_top _ ⊤) (le_preimage_top _ ⊤), kappa_d, kappa_d, appLE_top]
  change (toTsze O N ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map l).toRingHom)).appTop b)).snd = _
  rw [show toTsze O N ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map l).toRingHom)).appTop b) = TrivSqZeroExt.map l (toTsze O M b) from
    congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (TrivSqZeroExt.map l).toRingHom)) b)]
  simp

end GlobalTheory.SqZeroPt
