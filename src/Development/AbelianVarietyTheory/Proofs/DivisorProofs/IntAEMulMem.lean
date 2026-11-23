module

public import Formalism.UnipotentAdelicQuotients.ThmBInHecke
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

open scoped TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.IntegralAdeleProducts

theorem intAf_mul {F : Type} [Field F] [NumberField F] {a b : FiniteAdeleRing (𝓞 F) F}
    (ha : a ∈ HeckeCharacterZeroLocus.ThmBIn.intAf F) (hb : b ∈ HeckeCharacterZeroLocus.ThmBIn.intAf F) : a * b ∈ HeckeCharacterZeroLocus.ThmBIn.intAf F :=
  fun v => mul_mem (ha v) (hb v)

theorem intAE_mul_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {s t : FiniteAdeleRing (𝓞 F) F ⊗[F] E}
    (hs : s ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E) (ht : t ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E) :
    s * t ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := by
  unfold HeckeCharacterZeroLocus.ThmBIn.intAE at hs ht
  induction hs using AddSubgroup.closure_induction with
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx
  | mem x hx =>
    obtain ⟨a, ha, p, rfl⟩ := hx
    induction ht using AddSubgroup.closure_induction with
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | neg x _ hx => rw [mul_neg]; exact neg_mem hx
    | mem y hy =>
      obtain ⟨b, hb, q, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a * b, intAf_mul ha hb, p * q, ?_⟩
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      rfl

end GlobalTheory.IntegralAdeleProducts
