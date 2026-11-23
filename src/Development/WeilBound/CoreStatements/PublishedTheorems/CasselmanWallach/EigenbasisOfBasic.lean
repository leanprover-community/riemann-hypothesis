module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace EigenspaceDecomposition

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}

abbrev Es (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (μ : ℝ) : Submodule ℂ V :=
  Module.End.eigenspace (casimirK ε E) (μ : ℂ)

theorem mem_Es {μ : ℝ} {v : V} : v ∈ Es ε E μ ↔ Eig ε E μ v :=
  Module.End.mem_eigenspace_iff

theorem fd (h : Mod ε E) (μ : ℝ) : FiniteDimensional ℂ (Es ε E μ) := by
  haveI := h.fin μ
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {v : V | ∃ μ' ≤ μ, Eig ε E μ' v}) ?_
  intro v hv
  exact Submodule.subset_span ⟨μ, le_rfl, mem_Es.mp hv⟩

end EigenspaceDecomposition

open EigenspaceDecomposition in
theorem eigenbasis_of_basic : A0 → EigenbasisExists := by
  intro hA n ε V _ _ E h
  obtain ⟨hsym, hnn, -, -⟩ := hA n ε V E h
  haveI : ∀ μ : ℝ, FiniteDimensional ℂ (Es ε E μ) := fun μ => fd h μ
  let f : (Σ μ : ℝ, Fin (Module.finrank ℂ (Es ε E μ))) → V :=
    fun i => ((stdOrthonormalBasis ℂ (Es ε E i.1)) i.2 : V)
  have hOF : OrthogonalFamily ℂ (fun μ : ℝ => Es ε E μ) (fun μ => (Es ε E μ).subtypeₗᵢ) :=
    (LinearMap.IsSymmetric.orthogonalFamily_eigenspaces (T := casimirK ε E) hsym).comp
      (f := fun μ : ℝ => (μ : ℂ)) Complex.ofReal_injective
  have hon : Orthonormal ℂ f :=
    hOF.orthonormal_sigma_orthonormal (fun μ => (stdOrthonormalBasis ℂ (Es ε E μ)).orthonormal)
  have hli : LinearIndependent ℂ f := hon.linearIndependent
  have hEs : ∀ μ : ℝ, ∀ v ∈ Es ε E μ, v ∈ Submodule.span ℂ (Set.range f) := by
    intro μ v hv
    have key := (stdOrthonormalBasis ℂ (Es ε E μ)).sum_repr ⟨v, hv⟩
    have hv' : v = ∑ i, ((stdOrthonormalBasis ℂ (Es ε E μ)).repr ⟨v, hv⟩ i) •
        ((stdOrthonormalBasis ℂ (Es ε E μ)) i : V) := by
      have := congrArg Subtype.val key
      rw [Submodule.coe_sum] at this
      simpa using this.symm
    rw [hv']
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨μ, i⟩, rfl⟩)
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range f) := by
    rw [← h.span, Submodule.span_le]
    rintro v ⟨μ, hμ⟩
    exact hEs μ v (mem_Es.mpr hμ)
  have heig : ∀ i, Eig ε E i.1 (f i) := fun i =>
    mem_Es.mp ((stdOrthonormalBasis ℂ (Es ε E i.1)) i.2).2
  refine ⟨_, Module.Basis.mk hli hsp, fun i => i.1, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hon
  · intro i
    simpa using heig i
  · intro i
    refine hnn i.1 (f i) (heig i) ?_
    intro h0
    have := hon.1 i
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  · intro R
    haveI := h.fin R
    let W := Submodule.span ℂ {v : V | ∃ μ ≤ R, Eig ε E μ v}
    let g : {i : (Σ μ : ℝ, Fin (Module.finrank ℂ (Es ε E μ))) | i.1 ≤ R} → W :=
      fun i => ⟨f i.1, Submodule.subset_span ⟨i.1.1, i.2, heig i.1⟩⟩
    have hg : LinearIndependent ℂ g :=
      LinearIndependent.of_comp W.subtype (hli.comp _ Subtype.val_injective)
    haveI := hg.finite
    exact Set.toFinite _

end PositivityTheory.CW

end
