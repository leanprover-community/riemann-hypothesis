module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfUnitFrobeniusEqMulStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompatibleRootsOfUnityAndTiltPadic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineThetaEqZeroIffFontaineXiElementDvd
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Kernel
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_isPer : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ τ : Ainf l, bk.IsPer τ := by
  intro l hl K bk
  obtain ⟨ζ, e, h0, -, h1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : e.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps e := ⟨he, fun hh => h1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  set x : Ainf l := Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e) with hx
  have hxl : x ^ l = Per.tm e := by
    rw [hx, ← map_pow, frobeniusEquiv_symm_pow_p]
  have hφx : WittVector.frobenius x = Per.tm e := by
    rw [hx, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def,
      frobeniusEquiv_symm_pow_p]
  have hξ : GlobalTheory.MemLoc.xi e * (x - 1) = Per.tm e - 1 := by
    rw [GlobalTheory.MemLoc.xi, ← hx, geom_sum_mul, hxl]
  have hsp : Ideal.span {bk.ev bk.E} = Ideal.span {GlobalTheory.MemLoc.xi e} :=
    bk.span_ev.trans (GlobalTheory.MemLoc.ker_theta_eq_span_xi hE)
  obtain ⟨ω, hω⟩ := Ideal.span_singleton_eq_span_singleton.1 hsp.symm
  obtain ⟨η, hη⟩ := GlobalTheory.T.exists_ainf_unit_frobenius_eq_mul l ω
  refine ⟨(x - 1) * η, ?_, e, ω * η, hE, ?_⟩
  · rw [map_mul, map_sub, map_one, hφx, hη, ← hω, ← hξ]
    ring
  · rw [map_mul, map_sub, map_one, hφx, hη, Units.val_mul]
    rw [mul_comm]
end GlobalTheory.BSP
