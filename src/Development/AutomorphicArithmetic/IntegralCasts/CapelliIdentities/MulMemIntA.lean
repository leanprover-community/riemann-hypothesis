module

public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
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

namespace UpperTheory.Reformulated.B.Uc13

open IsDedekindDomain NumberField
open scoped TensorProduct

@[reducible] noncomputable def Af (F : Type) [Field F] [NumberField F] : Type :=
  FiniteAdeleRing (RingOfIntegers F) F

@[reducible] noncomputable def Fv (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) : Type :=
  v.adicCompletion F

theorem aux3 (F : Type) [Field F] [NumberField F]
    (i : HeightOneSpectrum (RingOfIntegers F)) :
    SubringClass (ValuationSubring (Fv F i)) (Fv F i) :=
  inferInstance

theorem aux4 (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) (x : F) :
    RestrictedProduct.evalRingHom (fun w => Fv F w) v (algebraMap F (Af F) x) =
      RestrictedProduct.evalRingHom (fun w => Fv F w) v (algebraMap F (Af F) x) :=
  rfl

noncomputable def evalV (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) : Af F →ₐ[F] Fv F v where
  toRingHom := RestrictedProduct.evalRingHom (fun w => Fv F w) v
  commutes' := aux4 F v

noncomputable def intAf (F : Type) [Field F] [NumberField F] : Set (Af F) :=
  {a | ∀ (v : HeightOneSpectrum (RingOfIntegers F)), evalV F v a ∈ v.adicCompletionIntegers F}

noncomputable def intA (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] :
    AddSubgroup (TensorProduct F (Af F) E) :=
  AddSubgroup.closure {y | ∃ a ∈ intAf F, ∃ x : RingOfIntegers E, y = a ⊗ₜ[F] (x : E)}

theorem mul_mem_intA (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {x y : TensorProduct F (Af F) E}
    (hx : x ∈ intA F E) (hy : y ∈ intA F E) : x * y ∈ intA F E := by
  unfold intA at *
  induction hx, hy using AddSubgroup.closure_induction₂ with
  | mem x y hx hy =>
    obtain ⟨a, ha, s, rfl⟩ := hx
    obtain ⟨b, hb, t, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨a * b, ?_, s * t, ?_⟩
    · intro v
      rw [map_mul]
      exact mul_mem (ha v) (hb v)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]
      rfl
  | zero_left x hx => rw [zero_mul]; exact zero_mem _
  | zero_right x hx => rw [mul_zero]; exact zero_mem _
  | add_left x y z hx hy hz h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | add_right y z x hy hz hx h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg_left x y hx hy h => rw [neg_mul]; exact neg_mem h
  | neg_right x y hx hy h => rw [mul_neg]; exact neg_mem h

end UpperTheory.Reformulated.B.Uc13
