module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInterOfSubfield
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterNormOneUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqSumSplitPlaceParts
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.SplitCharAlg

open Formalism.L2.Host
open scoped TensorProduct

theorem isAlgebraic_loc {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} {n : I → ℤ}
    {χ : HChar E} (h : χ.HasInf φ n) (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ) :
    IsAlgebraic ℚ ((χ.loc v x : ℂˣ) : ℂ) := by
  have h2 : (χ ^ 2).HasInf φ (fun i => 2 * n i) := by
    intro k
    have e1 : (((χ ^ 2).inf k : ℂˣ) : ℂ) = ((χ.inf k : ℂˣ) : ℂ) ^ 2 := rfl
    rw [e1, h k, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    show _ = _ ^ (2 * n i)
    rw [mul_comm, zpow_mul]
    norm_cast
  obtain ⟨M, hM, hv⟩ := GlobalTheory.HeckeLocVals.locVals_of_even h2
  have hx := hv v x
  have e2 : (((χ ^ 2).loc v x : ℂˣ) : ℂ) = ((χ.loc v x : ℂˣ) : ℂ) ^ 2 := rfl
  rw [e2] at hx
  have hint : IsIntegral ℚ (((⟨_, hx⟩ : M) : ℂ)) := (IsIntegral.of_finite ℚ (⟨_, hx⟩ : M)).map M.val
  exact IsAlgebraic.of_pow two_pos hint.isAlgebraic


open GlobalTheory.AdelicU GlobalTheory.AdelicU.Supp GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in
theorem exists_locIdele {D : D7} {e : AE D} (he : IsSplitIdem D e) (x : (AE D)ˣ) (hx : (x : AE D) = e * x + (1 - e)) :
    ∃ (w : HeightOneSpectrum (𝓞 D.host.E)) (y : (w.adicCompletion D.host.E)ˣ), x = GlobalTheory.LFun.locIdele D.host.F w y := by
  obtain ⟨v, τ, rfl⟩ := isSplitIdem_iff_exists.1 he
  have hA : At (evFin D.host.F v) (splitIdemAd (isCMExt_host D) τ) := by
    intro u hu
    rw [Algebra.smul_def, mul_comm]
    change singleTens D.host.E v _ * _ = 0
    rw [singleTens_mul]
    have : compFin D.host.F D.host.E v (algebraMap (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) u) = 0 := by
      change (evFin D.host.F v u) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      rw [hu, TensorProduct.zero_tmul]
    rw [this, mul_zero, map_zero]
  have h1 : (x : AE D) - 1 = splitIdemAd (isCMExt_host D) τ * ((x : AE D) - 1) := by
    rw [mul_sub, mul_one]
    nth_rewrite 1 [hx]
    ring
  refine ⟨_, _, GlobalTheory.ChrLocal.eq_locIdele_splitPrime (isCMExt_host D) τ x ?_ ?_⟩
  · intro u hu
    rw [h1, ← smul_mul_assoc, hA u hu, zero_mul]
  · obtain ⟨-, e0⟩ := GlobalTheory.LatSplit.piW_splitIdemAd (isCMExt_host D) τ
    rw [hx, map_add (f := _), map_mul, map_sub, map_one, e0]
    ring

end GlobalTheory.SplitCharAlg

namespace GlobalTheory.SplitCharAlg

end GlobalTheory.SplitCharAlg
