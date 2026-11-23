module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoConstOfGenericIsoDvr
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.DimEqZero

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_lineBundleIso_const_of_genericIso_dvr : ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ (P M : LB G.left) (N : LB (pullback G.hom (spMap (algebraMap W K')))), P.IsLB → M.IsLB → N.IsLB → ∀ (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N) (w₁ : LB.Iso (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N), w.IsGen → w₁.IsGen → ∃ (v : LB.Iso P M) (c : K'), v.IsGen ∧ ∀ (n : N.ι) (i : P.ι) (m : M.ι) (hle : N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) ≤ pullback.fst G.hom (spMap (algebraMap W K')) ⁻¹ᵁ (M.U m ⊓ P.U i)), GlobalTheory.AbLaw.rs _ (inf_le_left : N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) ≤ N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i)) (w₁.s (n, fun _ => i)).val = GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) _ c * ((pullback.fst G.hom (spMap (algebraMap W K'))).appLE (M.U m ⊓ P.U i) _ hle).hom (v.s (m, i)).val * GlobalTheory.AbLaw.rs _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right : N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) ≤ N.U n ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m)) (w.s (n, fun _ => m)).val := by
  first | exact @GlobalTheory.GenericIsoConst.exists_iso_const_of_generic | exact GlobalTheory.GenericIsoConst.exists_iso_const_of_generic | (intros; apply GlobalTheory.GenericIsoConst.exists_iso_const_of_generic <;> assumption)
