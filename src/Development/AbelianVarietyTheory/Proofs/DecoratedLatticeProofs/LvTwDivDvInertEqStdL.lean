module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Formalism.SatakeDualWeyl.StatementG
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.LFun

theorem LvTw_div_dv_inert_eq_stdL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (B : Fam E) (m : HeightOneSpectrum (𝓞 E) → ℂˣ) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (r b : ℕ) (α : Fin (r / 2) → ℂˣ) (s : ℂ), Module.finrank F E = 2 → IsInertAt F E v w → Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v → B w = bcParam r α → LvTw B m v (s + 1 / 2) / dv E r b v s = GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.stdL (qV F v) r α (((m w)⁻¹ : ℂˣ) : ℂ) (s + 1 / 2) / GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.dFac (qV F v) r b s := by
  intro F E _ _ _ _ _ B m v w r b α s h2 hw hU hB
  have hv := InertChart.under_eq_iff hw
  have hq := InertChart.absNorm_eq h2 hw
  have hq0 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (one_lt_absNorm v).ne_bot
  have hns := not_isSplit_of_isInertAt hw
  rw [LvTw_inert B m hv hq, hB]
  congr 1
  · rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.stdL, Units.val_inv_eq_inv_val]
    congr 2
    rw [npow, show qV F v = Ideal.absNorm v.asIdeal from rfl, pow_two,
      show -(2 * (s + 1 / 2)) = -(s + 1 / 2) + -(s + 1 / 2) by ring, Complex.cpow_add _ _ hq0,
      Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  · rw [dv, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.dFac]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [locL, etaFam_of_unram hU, eulerFac_singleton, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.etaL, Units.val_pow_eq_pow_val, npow,
      show qV F v = Ideal.absNorm v.asIdeal from rfl]
    have he : ((etaU E v : ℂˣ) : ℂ) = -1 := by simp [etaU, hns]
    rw [he]

end GlobalTheory.LFun
