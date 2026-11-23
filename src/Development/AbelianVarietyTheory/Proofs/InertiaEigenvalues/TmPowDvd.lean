module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalMapSurjective
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem tm_pow_dvd : ∀ (l : ℕ) [Fact l.Prime] (x : Fl l), ‖sh x‖ ≤ ‖(l : ℂ_[l])‖ →
    (l : Acris l) ∣ algebraMap (Ainf l) (Acris l) (tm x) ^ l := by
  intro l _ x hx
  have hmem : x.untilt ∈ (Ideal.span {(l : OC l)}) ^ 1 := by
    rw [GlobalTheory.RingBasics.mem_span_pow_OC, pow_one]
    exact hx
  rw [pow_one] at hmem
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
  obtain ⟨z, hz⟩ := GlobalTheory.MemLoc.FundOnto.untilt_surjective l c
  have hk := GlobalTheory.MemLoc.FundOnto.dvd_pow_of_ker l (tm x - (l : Ainf l) * tm z) (by
    rw [map_sub, map_mul, map_natCast, GlobalTheory.MemLoc.FundOnto.theta_tm,
      GlobalTheory.MemLoc.FundOnto.theta_tm, hz, ← hc, mul_comm, sub_self])
  rw [map_sub, map_mul, map_natCast] at hk
  generalize algebraMap (Ainf l) (Acris l) (tm x) = X at hk ⊢
  generalize algebraMap (Ainf l) (Acris l) (tm z) = Z at hk
  have h1 : ((l : ℕ) : Acris l) ∣ X - (X - (l : Acris l) * Z) := ⟨Z, by ring⟩
  have h2 := h1.trans (sub_dvd_pow_sub_pow _ _ l)
  have := dvd_add h2 hk
  simpa using this

end GlobalTheory.PSer
