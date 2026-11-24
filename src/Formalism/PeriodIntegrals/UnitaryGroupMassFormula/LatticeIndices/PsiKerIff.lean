module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondSplitTensorVector
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

namespace MassDataIdxCore

open Matrix

variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (O : ValuationSubring K) {n : Type} [Fintype n]
  [DecidableEq n]

def toO (M : Matrix n n K) (hM : IntM O M) : Matrix n n O := fun i j => ⟨M i j, hM i j⟩

theorem toO_map (M : Matrix n n K) (hM : IntM O M) : (toO O M hM).map (algebraMap O K) = M := by
  ext i j
  rfl

theorem map_inj : Function.Injective fun M : Matrix n n O => M.map (algebraMap O K) := by
  intro M N h
  ext i j
  have h1 := congrFun (congrFun h i) j
  exact h1

variable (θ : T ≃ₐ[K] K × K) (J : Matrix n n T) (P : GL n K) {H : Type} [Group H] (m : H →* GL n T)
  (hK : ∀ h x, x ∈ Lat O θ J P ↔ ((m h : GL n T) : Matrix n n T) *ᵥ x ∈ Lat O θ J P)

include hK in
theorem int_of (h : H) : IntM O (conjPrime₂ θ P (m h)) :=
  conjP_int O θ J P (m h) fun x hx => (hK h x).mp hx

def psiU (h : H) : GL n O :=
  ⟨toO O _ (int_of O θ J P m hK h), toO O _ (int_of O θ J P m hK h⁻¹), by
    apply map_inj O
    simp only [Matrix.map_mul, toO_map, ← conjP_mul, ← map_mul, mul_inv_cancel, map_one, conjP_one]
    exact (Matrix.map_one _ (map_zero _) (map_one _)).symm, by
    apply map_inj O
    simp only [Matrix.map_mul, toO_map, ← conjP_mul, ← map_mul, inv_mul_cancel, map_one, conjP_one]
    exact (Matrix.map_one _ (map_zero _) (map_one _)).symm⟩

theorem psiU_map (h : H) : ((psiU O θ J P m hK h : GL n O) : Matrix n n O).map (algebraMap O K) =
    conjPrime₂ θ P (m h) :=
  toO_map O _ (int_of O θ J P m hK h)

def psi : H →* GL n O where
  toFun := psiU O θ J P m hK
  map_one' := by
    apply Units.ext
    apply map_inj O
    simp only [psiU_map, map_one, conjP_one, Units.val_one]
    exact (Matrix.map_one _ (map_zero _) (map_one _)).symm
  map_mul' _ _ := by
    apply Units.ext
    apply map_inj O
    simp only [Units.val_mul, Matrix.map_mul, psiU_map, map_mul, conjP_mul]

theorem psi_map (h : H) : ((psi O θ J P m hK h : GL n O) : Matrix n n O).map (algebraMap O K) =
    conjPrime₂ θ P (m h) :=
  psiU_map O θ J P m hK h

theorem psi_ker_iff (c : O) (h : H) :
    (∀ i j, (((psi O θ J P m hK h : GL n O) : Matrix n n O) - 1) i j ∈ Ideal.span {c}) ↔
      ∀ i j, ∃ w ∈ O, (conjPrime₂ θ P (m h) - 1) i j = (c : K) * w := by
  have key : ∀ i j, ((((psi O θ J P m hK h : GL n O) : Matrix n n O) - 1) i j : K) =
      (conjPrime₂ θ P (m h) - 1) i j := by
    intro i j
    rw [← psi_map O θ J P m hK h]
    simp [Matrix.sub_apply, Matrix.one_apply]
    split_ifs <;> simp
  constructor
  · intro H1 i j
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (H1 i j)
    refine ⟨b, b.2, ?_⟩
    rw [← key, ← hb]
    push_cast
    ring
  · intro H1 i j
    obtain ⟨w, hw, hwe⟩ := H1 i j
    refine Ideal.mem_span_singleton'.mpr ⟨⟨w, hw⟩, ?_⟩
    apply Subtype.ext
    rw [key]
    rw [hwe]
    push_cast
    ring

end MassDataIdxCore
