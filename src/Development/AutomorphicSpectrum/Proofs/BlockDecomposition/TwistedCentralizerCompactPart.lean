module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CentOk

theorem centraliser_hyps : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (θ : G →* G), Continuous θ → ∀ (K I C : Subgroup G) (δ : G), IsCompact (K : Set G) → IsOpen (I : Set G) → IsCompact (C : Set G) → cptPart (twCent θ δ) = twCent θ δ ⊓ C → ∀ x : G, twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent θ δ) ∧ (twCent θ δ ⊓ I.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent θ δ)) ≠ 0 := by
  intro G _ _ _ _ θ hθ K I C δ hK hI hC hcpt x
  have hTc : IsClosed (twCent θ δ : Set G) := by
    have : (twCent θ δ : Set G) = {g | g * δ = δ * θ g} := rfl
    rw [this]
    exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul hθ)
  have hconj : Continuous fun a : G => x * a * x⁻¹ := by fun_prop
  constructor
  · have hKx : IsCompact ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
      rw [Subgroup.coe_map]
      exact hK.image hconj
    intro g hg
    apply Subgroup.subset_closure
    refine ⟨hg.1, ?_⟩
    have hzp : (Subgroup.zpowers g : Set G) ⊆ (K.map (MulAut.conj x).toMonoidHom : Subgroup G) :=
      (Subgroup.zpowers_le (G := G) (H := K.map (MulAut.conj x).toMonoidHom)).2 hg.2
    exact hKx.of_isClosed_subset isClosed_closure (closure_minimal hzp hKx.isClosed)
  · set A : Subgroup G := I.map (MulAut.conj x).toMonoidHom with hA
    have hAo : IsOpen (A : Set G) := by
      rw [hA, Subgroup.coe_map]
      exact (Homeomorph.mulLeft x |>.trans (Homeomorph.mulRight x⁻¹)).isOpenMap _ hI
    have hHc : IsCompact (cptPart (twCent θ δ) : Set G) := by
      rw [hcpt, Subgroup.coe_inf]
      exact hC.inter_left hTc
    have hHT : cptPart (twCent θ δ) ≤ twCent θ δ := by
      rw [hcpt]; exact inf_le_left
    have e : (twCent θ δ ⊓ A) ⊓ cptPart (twCent θ δ) = A ⊓ cptPart (twCent θ δ) := by
      ext g
      simp only [Subgroup.mem_inf]
      exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hHT h.2, h.1⟩, h.2⟩⟩
    rw [← Subgroup.inf_relIndex_right, e, Subgroup.inf_relIndex_right]
    haveI : CompactSpace (cptPart (twCent θ δ)) := isCompact_iff_compactSpace.mp hHc
    have ho : IsOpen ((A.subgroupOf (cptPart (twCent θ δ)) : Subgroup _) : Set (cptPart (twCent θ δ))) :=
      hAo.preimage continuous_subtype_val
    haveI := Subgroup.quotient_finite_of_isOpen _ ho
    exact Subgroup.index_ne_zero_of_finite

end GlobalTheory.CompanionTheory.CentOk
