module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Mathlib.NumberTheory.NumberField.CMField
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.HatCap

variable {E : Type} [Field E] [NumberField E]

theorem isOpen_integral :
    IsOpen {y : Af E | ∀ v : HeightOneSpectrum (𝓞 E), y v ∈ v.adicCompletionIntegers E} :=
  RestrictedProduct.isOpen_forall_mem
    (R := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (A := fun v : HeightOneSpectrum (𝓞 E) => (v.adicCompletionIntegers E : Set (v.adicCompletion E)))
    (fun v => Valued.isOpen_valuationSubring (v.adicCompletion E))

theorem mem_orderC_of_mem_hatO {c : Ideal (OF E)} (hc : c ≠ ⊥) {x : E} (hx : algebraMap E (Af E) x ∈ hatO c) :
    x ∈ orderC c := by
  obtain ⟨n, hnc, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  have hnE : algebraMap (OF E) E n ≠ 0 := by
    intro h
    apply hn0
    have h' : ((n : maximalRealSubfield E) : E) = 0 := h
    exact_mod_cast h'
  set m : E := algebraMap (OF E) E n with hm
  have hcont : Continuous fun z : Af E => (algebraMap E (Af E) x - z) * algebraMap E (Af E) m⁻¹ :=
    (continuous_const.sub continuous_id).mul continuous_const
  have hU := isOpen_integral.preimage hcont
  obtain ⟨_, hz, y, hy, rfl⟩ := mem_closure_iff.1 hx _ hU (by
    rw [Set.mem_preimage, sub_self, zero_mul]
    exact fun v => zero_mem _)
  obtain ⟨b, hb⟩ : ∃ b : 𝓞 E, algebraMap (𝓞 E) E b = (x - y) * m⁻¹ := by
    refine HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E _ fun v => ?_
    have h3 : (algebraMap E (Af E) ((x - y) * m⁻¹)) v ∈ v.adicCompletionIntegers E := by
      rw [map_mul, map_sub]; exact hz v
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).symm.trans_le
      ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h3)
  have hxy : x = y + algebraMap (𝓞 E) E (b * algebraMap (OF E) (𝓞 E) n) := by
    have : algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) n) = m := rfl
    rw [map_mul, hb, this, mul_assoc, inv_mul_cancel₀ hnE]; ring
  rw [hxy]
  refine add_mem hy (mem_orderC.2 ⟨0, _, Ideal.mul_mem_left _ b (Ideal.mem_map_of_mem _ hnc), by simp⟩)

theorem lattice_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → lattice c 1 = (orderC c : Set E) := by
  intro E _ _ _ c hc
  ext x
  rw [mem_lattice, inv_one, Units.val_one, mul_one]
  exact ⟨mem_orderC_of_mem_hatO hc, algebraMap_mem_hatO⟩

end GlobalTheory.CMVal.HatCap
