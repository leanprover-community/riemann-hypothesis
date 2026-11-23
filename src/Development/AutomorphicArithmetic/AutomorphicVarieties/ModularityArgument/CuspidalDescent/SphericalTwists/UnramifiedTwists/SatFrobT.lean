module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubquotSmIndCongr
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonFactorRecCompatible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodToralOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalSatakeEqLanglandsQuotientUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSteinberg
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FixedNeBotOfEquiv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.GalUnitaryT
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import GroundTheory.ProfiniteCohomology.LocalClassFormation.UnramifiedRes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Desc.W.SatakeFrobeniusEigenvalues

open Polynomial GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped commutatorElement

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem rec_diag {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRecT h rc) (x : IrrGL (k := w.adicCompletion E))
    (α : Fin x.1 → ℂˣ) (hα : HasSatake x.rep α) : rc x = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := by
  obtain ⟨a, ha, H⟩ := H
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have hL := GlobalTheory.T.spherical_satake_eq_langlandsQuotient_unramified Pr.exh Pr.multi Pr.cos Pr.zel GlobalTheory.RecT.geometricLemma_holds Pr.bz (w.adicCompletion E) x α hα
  rw [Fin.univ_val_map] at hL
  rw [H.langlands _ x hL, segSum, List.map_ofFn, ← SatakeLaw.sumList_ofFn_diag]
  congr 1
  refine List.ofFn_inj.mpr (funext fun i => ?_)
  simp only [Function.comp_apply, Segment.single, Segment.first_ofFirst, Segment.len_ofFirst, Nat.cast_one, sub_self,
    zero_div, WD.lpTw_zero, Test.lpChar_lpSp_one, H.one]
  exact Test.lpOfChar_unrChar ha (α i) _

private theorem rec_algNorm_diag {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRecT h rc) {n : ℕ}
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B) :
    ∃ α : Fin n → ℂˣ, B = Finset.univ.val.map α ∧
      rc (algNorm σ) = WD.mk (WDRep.diag h fun i => (α i)⁻¹ * qPow w ((1 - (n : ℝ)) / 2)) := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨α, hαB, hα⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ B).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.2 ⟨⟨σ.smooth, σ.irred⟩, hB⟩)
  refine ⟨α, hαB.symm, ?_⟩
  have φ := IrrGL.equivOf σ.ρ σ.smooth σ.irred
  have e : rc (IrrGL.of σ.ρ σ.smooth σ.irred) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) :=
    rec_diag H (IrrGL.of σ.ρ σ.smooth σ.irred) α ⟨IrrRep.irr _, fixed_ne_bot_of_equiv φ hα.2.1,
      (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hα.2.2⟩
  obtain ⟨a, ha, L⟩ := H
  rw [algNorm, L.nu, e, WD.lpTw_mk]
  refine WD.sound ⟨.refl _ _, fun g v => funext fun i => ?_, fun v => rfl⟩
  simp [mul_zpow, mul_comm, mul_left_comm, mul_assoc]

private theorem gd_diag {n : ℕ} (c : Fin n → ℂˣ) : Z.Win.Gd (WD.mk (WDRep.diag h c)) := by
  refine ⟨fun s t => ?_, WD.unr_mono0 _ ((WD.unr_mk _).2 (WDRep.unr_diag _))⟩
  have hd : deg (⁅s, t⁆ : Weil h) = 0 := by
    rw [commutatorElement_def, deg_mul, deg_mul, deg_mul, deg_inv, deg_inv]
    ring
  show WD.charPol _ _ = _
  rw [WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd, hd]
  simp

private theorem val_inv_eq (n : ℕ) (a : ℂˣ) :
    (((a⁻¹ * qPow w ((1 - (n : ℝ)) / 2) : ℂˣ) : ℂ)) ^ (-1 : ℤ) =
      ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (a : ℂ) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), zpow_neg_one, Units.val_mul, mul_inv, Units.val_inv_eq_inv_val, inv_inv,
    coe_qPow, ← Complex.cpow_neg, mul_comm]
  congr 2
  push_cast
  ring

end UpperTheory.V.Z.Desc.W.SatakeFrobeniusEigenvalues

