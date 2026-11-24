module

public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PositivityTheory.ThK

open NumberField IsDedekindDomain GlobalTheory.AdelicU

theorem map_eq_of_ncard_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Algebra.Unramified (𝓞 F) (𝓞 E)] (v : HeightOneSpectrum (𝓞 F)) (h : (v.asIdeal.primesOver (𝓞 E)).ncard = 1) :
    ∃ w : HeightOneSpectrum (𝓞 E), Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = w.asIdeal := by
  classical
  haveI := v.isMaximal
  obtain ⟨P, hP⟩ := Set.ncard_eq_one.1 h
  have hm : P ∈ v.asIdeal.primesOver (𝓞 E) := hP ▸ rfl
  haveI := hm.1
  haveI := hm.2
  have h0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
  refine ⟨⟨P, hm.1, h0⟩, ?_⟩
  have e : P.ramificationIdx (𝓞 F) = 1 := P.ramificationIdx_eq_one (𝓞 F)
  have := Ideal.map_algebraMap_eq_finsetProd_pow (R := 𝓞 E) v.ne_bot
  rw [this]
  simp [hP, e]

theorem inert_of_local : InertOf := by
  intro F E _ _ _ _ _ σ B hB v he
  haveI := hB.unram
  haveI := v.isMaximal
  have h1 := ncard_primesOver_le_two hB.cm v
  have h2 : (v.asIdeal.primesOver (𝓞 E)).ncard ≠ 2 := fun h =>
    not_nonempty_iff.2 he ((nonempty_split_iff hB.cm).2 h)
  have h3 : 0 < (v.asIdeal.primesOver (𝓞 E)).ncard := Nat.pos_of_ne_zero (IsDedekindDomain.primesOver_ncard_ne_zero _ _)
  exact map_eq_of_ncard_eq_one v (by omega)

end PositivityTheory.ThK
