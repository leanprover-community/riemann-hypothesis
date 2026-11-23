module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroPt

open GlobalTheory.LieVB GlobalTheory.Conormal

theorem kappa_cotMap_cst_smul (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M]
    [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (A : Over (Sp O)) [GrpObj A] (z : TM O M ⟶ A)
    (h : zeroSec O M ≫ z = η[A]) (c : O) (w : Γ(omega A, ⊤)) :
    kappa O M ((cotMap z h).app ⊤ (cst O c • w)) = c • kappa O M ((cotMap z h).app ⊤ w) := by
  rw [show (cotMap z h).app ⊤ (cst O c • w) = cst O c • (cotMap z h).app ⊤ w from
    (QCoh.appLinear (cotMap z h) ⊤).map_smul (cst O c) w]
  obtain ⟨b, hb⟩ := (isChart O M).d_surjective (sec_hom (zeroSec O M)) ((cotMap z h).app ⊤ w)
  rw [← hb]
  have key : cst O c • d (sec_hom (zeroSec O M)) (isChart O M).le b =
      d (sec_hom (zeroSec O M)) (isChart O M).le ((TM O M).hom.appLE ⊤ ⊤ le_top (cst O c) * b) := by
    rw [d_mul]
    erw [d_base (sec_hom (zeroSec O M)) (isChart O M).le le_top (cst O c)]
    rw [smul_zero, add_zero]
    erw [appLE_base (sec_hom (zeroSec O M)) _ _ le_rfl]
    rfl
  rw [key, kappa_d, kappa_d, map_mul, toTsze_base, TrivSqZeroExt.snd_mul]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem Phi_smul (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M]
    [IsCentralScalar O M] (A : Over (Sp O)) [GrpObj A] (z : TM O M ⟶ A)
    (h : zeroSec O M ≫ z = η[A]) (c : O) (w : Wmod A) :
    Phi z h (c • w) = c • Phi z h w :=
  kappa_cotMap_cst_smul O M A z h c w

end GlobalTheory.SqZeroPt
