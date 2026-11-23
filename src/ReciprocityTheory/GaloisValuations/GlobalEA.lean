module

public import ReciprocityTheory.Hypotheses.Descent
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Pointwise

namespace ReciprocityTheory.Gal

open Formalism.ConjugateSelfDual ReciprocityTheory.Hyp

section res

variable {F L Ω : Type*} [Field F] [Field L] [Field Ω] [Algebra F L] [Algebra F Ω] [Algebra L Ω]
  [IsScalarTower F L Ω]

@[simp] theorem resGal_apply (σ : G L Ω) (x : Ω) : resGal F L Ω σ x = σ x := rfl

theorem resGal_injective : Function.Injective (resGal F L Ω) := fun σ τ h =>
  AlgEquiv.ext fun x => by simpa using DFunLike.congr_fun h x

theorem continuous_resGal [Algebra.IsAlgebraic F Ω] : Continuous (resGal F L Ω) := by
  refine continuous_of_continuousAt_one (resGal F L Ω) ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨E, hE, hEs⟩ := (krullTopology_mem_nhds_one_iff F Ω s).1 hs
  let b := Module.finBasis F E
  let S : Set Ω := Set.range (fun i => (b i : Ω))
  have hint : ∀ x ∈ S, IsIntegral L x := fun x _ =>
    (Algebra.IsIntegral.isIntegral (R := F) x).tower_top
  have : FiniteDimensional L (IntermediateField.adjoin L S) :=
    IntermediateField.finiteDimensional_adjoin hint
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  refine ⟨IntermediateField.adjoin L S, this, fun σ hσ => hEs ?_⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  have hb : ∀ i, σ (b i : Ω) = b i := fun i =>
    hσ _ (IntermediateField.subset_adjoin L S ⟨i, rfl⟩)
  intro x hx
  have hx' : x = ((⟨x, hx⟩ : E) : Ω) := rfl
  rw [hx', ← b.sum_repr ⟨x, hx⟩]
  simp only [IntermediateField.coe_sum, IntermediateField.coe_smul]
  change resGal F L Ω σ _ = _

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change σ (((b.repr ⟨x, hx⟩) i) • (b i : Ω)) = _
  rw [← algebraMap_smul L ((b.repr ⟨x, hx⟩) i) (b i : Ω), map_smul, hb]

theorem isAlgClosure_top [IsAlgClosure F Ω] : IsAlgClosure L Ω :=
  ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.tower_top (K := F) L⟩

theorem isClosedEmbedding_resGal [IsAlgClosure F Ω] [CharZero L] :
    Topology.IsClosedEmbedding (resGal F L Ω) := by
  have := isAlgClosure_top (F := F) (L := L) (Ω := Ω)
  have : T2Space (G F Ω) := krullTopology_t2
  exact continuous_resGal.isClosedEmbedding resGal_injective

end res

section places

variable {F L Ω : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω] [Algebra F L]
  [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω]


end places

end ReciprocityTheory.Gal
