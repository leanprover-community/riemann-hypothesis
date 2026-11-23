module

public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypePrimeSize

theorem k_pow_le_g {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (i : Fin 2) : D.R.k ^ 8 ≤ D.host.g i := by
  obtain ⟨Y, h1, -, -, h4⟩ := P.g_Y
  have hL : 0 ≤ L.sc.L := by
    unfold Scale.L; exact Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _
  have hb : 1 ≤ L.sc.b := by unfold Scale.b; exact Real.one_le_exp hL
  have hk : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have h2 : (D.R.k : ℝ) ≤ D.R.k * L.sc.b := le_mul_of_one_le_right hk hb
  have h3 : (D.R.k : ℝ) ^ 8 ≤ (D.R.k * L.sc.b) ^ 8 := pow_le_pow_left₀ hk h2 8
  have : (D.R.k : ℝ) ^ 8 ≤ D.host.g i := h3.trans (h1.trans (h4 i).1)
  exact_mod_cast this

theorem typePrime_large_and_ok : ∀ (D : D7) (L : SizeData₂ D), ParameterChoice' D L → ∀ k : Fin 2,
    Module.finrank ℚ D.host.E * D.R.r + 1 < D.host.g k ∧
      GlobalTheory.BadShare.PrimeOK (D.host.g k) D.host.q D.host.d := by
  intro D L P i
  have hg := k_pow_le_g P i
  have hE : Module.finrank ℚ D.host.E = 4 * D.R.ord := D.host.finrank_cmField
  have he := D.host.two_le_e
  have h4 : 2 ^ 2 ≤ 2 ^ D.R.e := Nat.pow_le_pow_right (by norm_num) he
  have hf := D.R.f_le_k
  have hfo : D.R.f = 2 * D.R.ord := rfl
  have ho : 2 ^ D.R.e ≤ D.R.ord := Nat.le_of_dvd D.R.ord_pos D.R.toFrame.two_pow_dvd_ord
  have hm := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have ht := D.R.rank_add_five_le
  have hk8 : 8 ≤ D.R.k := by omega
  have hr : D.R.r ≤ 2 * D.R.k := by unfold Ranks.r; omega
  have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; omega
  have hE' : Module.finrank ℚ D.host.E ≤ 2 * D.R.k := by
    have h2f : D.R.f = 2 * D.R.ord := rfl
    have hfk : D.R.f ≤ D.R.k := hf
    omega
  have hk6 : 8 ^ 6 ≤ D.R.k ^ 6 := Nat.pow_le_pow_left hk8 6
  have hk2 : 8 ^ 2 ≤ D.R.k ^ 2 := Nat.pow_le_pow_left hk8 2
  have hpow : 8 ^ 6 * D.R.k ^ 2 ≤ D.R.k ^ 8 := by
    calc 8 ^ 6 * D.R.k ^ 2 ≤ D.R.k ^ 6 * D.R.k ^ 2 := Nat.mul_le_mul_right _ hk6
      _ = D.R.k ^ 8 := by ring
  have hprod : Module.finrank ℚ D.host.E * D.R.r ≤ 4 * D.R.k ^ 2 := by
    calc Module.finrank ℚ D.host.E * D.R.r ≤ (2 * D.R.k) * (2 * D.R.k) := Nat.mul_le_mul hE' hr
      _ = 4 * D.R.k ^ 2 := by ring
  obtain ⟨hq, hd, hq8, hd16, -⟩ := D.host.hyp
  have hb := D.host.qd_big.1
  refine ⟨by omega, hq, hd, by omega, by omega, by omega, ?_, ?_, by omega⟩
  · have h1 : 5 * 1 ≤ D.R.t * D.R.r := Nat.mul_le_mul (by omega) hr1
    have h2 : 4 * D.R.t * D.R.r = 4 * (D.R.t * D.R.r) := by ring
    exact le_max_of_le_left (by omega)
  · have hc := D.ntypes.g_cond i
    have hdvd : 16 * D.host.q * D.host.d ∣ D.host.QS * D.host.q * D.host.d := by
      have h16 : 16 ∣ D.host.QS := (pow_dvd_pow 2 (by omega : 4 ≤ D.R.e + 2)).trans D.host.tower_dvd
      exact Nat.mul_dvd_mul_right (Nat.mul_dvd_mul_right h16 _) _
    refine hdvd.trans ⟨D.host.g i / (D.host.QS * D.host.q * D.host.d), ?_⟩
    have := Nat.div_add_mod (D.host.g i) (D.host.QS * D.host.q * D.host.d)
    omega

end GlobalTheory.TypePrimeSize
