module

public import Mathlib.Algebra.Central.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.TensorProduct.Basic
public import GroundTheory.Brauer.TensorSimple
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Brauer

open TensorProduct Algebra.TensorProduct

section CentralSimple

variable (K L A : Type*) [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A]

theorem center_baseChange_eq_bot [Algebra.IsCentral K A] :
    Subalgebra.center L (L ⊗[K] A) = ⊥ := by
  refine le_antisymm (fun x hx ↦ ?_) bot_le
  have hx' : x ∈ Subalgebra.center K (L ⊗[K] A) := by
    rw [Subalgebra.mem_center_iff] at hx ⊢
    exact hx
  rw [center_tensorProduct_eq_map_includeLeft] at hx'
  obtain ⟨l, -, rfl⟩ := hx'
  exact Algebra.mem_bot.mpr ⟨l, by simp [Algebra.TensorProduct.algebraMap_apply]⟩

instance isCentral_baseChange [Algebra.IsCentral K A] : Algebra.IsCentral L (L ⊗[K] A) :=
  ⟨(center_baseChange_eq_bot K L A).le⟩

instance isSimpleRing_baseChange [Algebra.IsCentral K A] [IsSimpleRing A] :
    IsSimpleRing (L ⊗[K] A) :=
  isSimpleRing_tensorProduct_of_right (K := K) (A := A) (B := L)

theorem finrank_baseChange_eq : Module.finrank L (L ⊗[K] A) = Module.finrank K A :=
  Module.finrank_baseChange

end CentralSimple

section CSA

universe u v w

end CSA


variable (K L M A : Type*) [CommSemiring K] [CommSemiring L] [CommSemiring M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M] [Semiring A] [Algebra K A]



variable (K L A : Type*) [CommSemiring K] [CommSemiring L] [Algebra K L] [Semiring A] [Algebra K A]
variable (n : Type*) [Fintype n] [DecidableEq n]



variable (K L A B : Type*) [CommSemiring K] [CommSemiring L] [Algebra K L] [Semiring A]
  [Algebra K A] [Semiring B] [Algebra K B]



universe u v w w'

variable {K : Type u} [Field K]


end GroundTheory.Brauer
