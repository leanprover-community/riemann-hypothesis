module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Isom

theorem haar_fd_phi : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (S : HSp D) (μ : Measure (WO S V')) (𝓕 : Set (WO S V')), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL V' S) 𝓕 μ → ∃ (ν : Measure (WO S V)) (𝓖 : Set (WO S V)), ν.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratL V S) 𝓖 ν ∧ ∀ u : WO S V → ENNReal, ∫⁻ w in 𝓕, u ((I.phi S).symm w) ∂μ = ∫⁻ w in 𝓖, u w ∂ν := by
  intro D V V' I S μ 𝓕 hμ h𝓕
  haveI hB : BorelSpace (WO S V) := ⟨rfl⟩
  haveI hB' : BorelSpace (WO S V') := ⟨rfl⟩
  have hc := I.continuous_phi S
  have hcs := I.continuous_phi_symm S
  have hrat : ∀ x, I.phi S x ∈ ratL V' S ↔ x ∈ ratL V S := by
    intro x
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨I.Q * z, ?_⟩
      have h1 := I.symm.phi_ratW S z
      have h2 : ratW V' S z = I.phi S x := hz
      rw [h2, ← I.phi_symm_apply, AddEquiv.symm_apply_apply] at h1
      exact h1.symm
    · rintro ⟨z, hz⟩
      refine ⟨I.P * z, ?_⟩
      have h1 := I.phi_ratW S z
      have h2 : ratW V S z = x := hz
      rw [h2] at h1
      exact h1.symm
  let m : WO S V ≃ᵐ WO S V' :=
    { toEquiv := (I.phi S).toEquiv
      measurable_toFun := hc.measurable
      measurable_invFun := hcs.measurable }
  have hmp : MeasurePreserving m (μ.map m.symm) μ :=
    (MeasurePreserving.symm m.symm ⟨m.symm.measurable, rfl⟩)
  have hmp' : MeasurePreserving (I.phi S) (μ.map (I.phi S).symm) μ := hmp
  refine ⟨μ.map (I.phi S).symm, I.phi S ⁻¹' 𝓕, AddEquiv.isAddHaarMeasure_map μ (I.phi S).symm hcs (by simpa using hc), ?_, ?_⟩
  · let f : ratL V' S → ratL V S := fun y => ⟨(I.phi S).symm y, (hrat _).1 (by simpa using y.2)⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b hab
        exact Subtype.ext ((I.phi S).symm.injective (congrArg Subtype.val hab))
      · intro x
        exact ⟨⟨I.phi S x, (hrat _).2 x.2⟩, Subtype.ext (by simp [f])⟩
    refine h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving hf ?_
    intro y x
    simp [f, AddSubgroup.vadd_def]
  · intro u
    have := hmp'.setLIntegral_comp_preimage_emb m.measurableEmbedding (fun b => u ((I.phi S).symm b)) 𝓕
    simpa using this.symm

end GlobalTheory.Mem.Isom
