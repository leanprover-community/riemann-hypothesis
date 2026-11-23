module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivativeTransitionUnitsIsoLineBundles
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

theorem _root_.GlobalTheory.T.logDerivative_transitionUnits_isoLineBundles : ∀ {Y Z : Scheme.{0}} (m : Y ⟶ Z) (L : LB Z) (M : LB Y) (wg : LB.Iso (L.pull m) M) (hwg : wg.IsGen) (j₁ j₂ : L.ι) (p₁ p₂ : M.ι) {B : Type} [CommRing B] (x : Sp B ⟶ Y) (w : Sp (DualNumber B) ⟶ Y) (hwx : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ w = x) (h₁ : ⊤ ≤ x ⁻¹ᵁ (M.U p₁ ⊓ (L.pull m).U (fun _ => j₁))) (h₂ : ⊤ ≤ x ⁻¹ᵁ (M.U p₂ ⊓ (L.pull m).U (fun _ => j₂))), (valR w _ (M.g p₁ p₂).val).snd * valR x _ (M.g p₁ p₂)⁻¹.val = (valR (w ≫ m) _ (L.g j₁ j₂).val).snd * valR (x ≫ m) _ (L.g j₁ j₂)⁻¹.val + ((valR w _ (wg.s (p₁, fun _ => j₁)).val).snd * valR x _ (wg.s (p₁, fun _ => j₁))⁻¹.val - (valR w _ (wg.s (p₂, fun _ => j₂)).val).snd * valR x _ (wg.s (p₂, fun _ => j₂))⁻¹.val) := by
  first | exact @GlobalTheory.CechKS.dlog_transition_iso | exact GlobalTheory.CechKS.dlog_transition_iso | (intros; apply GlobalTheory.CechKS.dlog_transition_iso <;> assumption)
