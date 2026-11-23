module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NormPderivIterLeOfAnalyticAt
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumTaylorCoordinateSpaceEntire
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LineDerivListCompForm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjMono
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

namespace GlobalTheory.FockTaylor

def curryL (ι : Type) (a b : ℕ) : (DVar ι a b → ℂ) →ₗ[ℂ] VCx ι a b where
  toFun w := fun τ i j => w (τ, i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem curryL_single {ι : Type} [DecidableEq ι] {a b : ℕ} (k : DVar ι a b) :
    curryL ι a b (Pi.single k 1) = Formalism.L2.Ker.coordX k := by
  funext τ i j
  obtain ⟨x, y, z⟩ := k
  simp [curryL, Formalism.L2.Ker.coordX, Pi.single_apply, Prod.ext_iff]

theorem derivAt0_eq_pderivIter {ι : Type} [Fintype ι] [DecidableEq ι] {a b : ℕ}
    (G : VCx ι a b → ℂ) (hG : Differentiable ℂ G) (m : DVar ι a b →₀ ℕ) :
    derivAt0 G m = GlobalTheory.pderivIter m (fun w => G (curryL ι a b w)) 0 := by
  have han : AnalyticAt ℂ G 0 := SCV.analyticOnNhd_of_differentiable hG Set.univ 0 (Set.mem_univ _)
  rw [derivAt0, GlobalTheory.pderivIter, GlobalTheory.pderivList, GlobalTheory.lineDerivList_comp_linearMap,
    ← GlobalTheory.lineDerivList_ofFn han]
  simp only [map_zero, List.map_map]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [curryL_single]

theorem coeff_taylor_eq_pderivIter {σ : Type} [Fintype σ] [DecidableEq σ] {f : (σ → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f 0) (α : σ →₀ ℕ) :
    MvPowerSeries.coeff α (GlobalTheory.taylor f) = GlobalTheory.pderivIter α f 0 / ∏ j, ((α j).factorial : ℂ) := by
  rw [GlobalTheory.coeff_taylor, GlobalTheory.dirPolyDeriv_monomial_eq_lineDerivList (l := α.toMultiset.toList)
    (by simp) _ hf, Nat.cast_prod, div_eq_inv_mul]
  rfl

end GlobalTheory.FockTaylor


open GlobalTheory.FockTaylor in
theorem GlobalTheory.FockTaylor.hasSum_derivAt0 : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (G : VCx ι a b → ℂ), Differentiable ℂ G → ∀ z₀ : VCx ι a b, HasSum (fun m : DVar ι a b →₀ ℕ => (m.prod fun k n => z₀ k.1 k.2.1 k.2.2 ^ n / (n.factorial : ℂ)) * derivAt0 G m) (G z₀) := by
  intro ι _ a b G hG z₀
  classical
  let L := LinearMap.toContinuousLinearMap (curryL ι a b)
  have hf : Differentiable ℂ (fun w => G (L w)) := hG.comp L.differentiable
  have hfa : AnalyticAt ℂ (fun w => G (L w)) 0 :=
    SCV.analyticOnNhd_of_differentiable hf Set.univ 0 (Set.mem_univ _)
  let c : (DVar ι a b →₀ ℕ) → ℂ := fun m => derivAt0 G m / ∏ j, ((m j).factorial : ℂ)
  have hne : ∀ m : DVar ι a b →₀ ℕ, (∏ j, ((m j).factorial : ℂ)) ≠ 0 := fun m =>
    Finset.prod_ne_zero_iff.mpr fun k _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hc : ∀ m, (∏ j, ((m j).factorial : ℂ)) * c m = GlobalTheory.pderivIter m (fun w => G (L w)) 0 :=
    fun m => by
      rw [mul_div_cancel₀ _ (hne m), derivAt0_eq_pderivIter G hG m]
      rfl
  have hc' : ∀ m, c m = MvPowerSeries.coeff m (GlobalTheory.taylor fun w => G (L w)) := fun m => by
    rw [coeff_taylor_eq_pderivIter hfa]
    show derivAt0 G m / _ = _
    rw [derivAt0_eq_pderivIter G hG m]
    rfl
  let w : DVar ι a b → ℂ := fun k => z₀ k.1 k.2.1 k.2.2
  have hs := GlobalTheory.EntireTaylor.summable_of_entire hf c hc w
  have ht := GlobalTheory.ProdThetaConj.tsum_of_entire hf c hc hc' w
  have hterm : ∀ m : DVar ι a b →₀ ℕ,
      (m.prod fun k n => z₀ k.1 k.2.1 k.2.2 ^ n / (n.factorial : ℂ)) * derivAt0 G m
        = c m * ∏ j, w j ^ m j := fun m => by
    rw [Finsupp.prod_fintype _ _ (by simp), Finset.prod_div_distrib]
    simp only [c, w]
    ring
  have hGz : G z₀ = G (L w) := rfl
  rw [hGz, ← ht]
  exact (hs.hasSum).congr_fun hterm
