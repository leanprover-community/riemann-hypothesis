module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalIdeal
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

variable {X : Scheme.{u}} {A : Type u} [CommRing A] [IsNoetherianRing A] [X.Over (Spec (.of A))]

attribute [local instance] algebraOfOver

variable (I : Ideal A) (F : X.Modules)

lemma exists_smulHom_eq_comp_idealSumMap (J : Ideal A) {a : A} (ha : a ∈ J) :
    ∃ h : F ⟶ (⨁ fun _ : Fin (idealGenNum J) => F),
      smulHom F (algebraMap A Γ(X, ⊤) a) = h ≫ idealSumMap F J := by
  rw [← span_idealGen J] at ha
  obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).1 ha
  refine ⟨biproduct.lift fun j => smulHom F (algebraMap A Γ(X, ⊤) (c j)), ?_⟩

  simp only [idealSumMap, biproduct.lift_desc, smulHom_comp_smulHom, ← map_mul, ← smulHom_sum,
  ← map_sum]
  rw [hc]

def idealPowOfMem {k : ℕ} (a : A) (ha : a ∈ I ^ k) : F ⟶ idealPow I F k :=
  kernel.lift _ (smulHom F (algebraMap A Γ(X, ⊤) a)) (by
    obtain ⟨h, hh⟩ := exists_smulHom_eq_comp_idealSumMap F (I ^ k) ha
    rw [hh, Category.assoc, cokernel.condition, comp_zero])

lemma idealPowOfMem_ι {k : ℕ} (a : A) (ha : a ∈ I ^ k) :
    idealPowOfMem I F a ha ≫ idealPowι I F k = smulHom F (algebraMap A Γ(X, ⊤) a) :=
  kernel.lift_ι _ _ _

end

end GroundTheory.Arith.SchemeCoh
