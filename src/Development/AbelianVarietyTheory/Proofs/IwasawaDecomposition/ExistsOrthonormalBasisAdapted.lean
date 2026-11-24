module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem

theorem exists_orthonormalBasis_adapted (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (I : Type) [Fintype I] [DecidableEq I] (p : I → Submodule ℂ E)
    (htop : (⨆ i, p i) = ⊤) (horth : ∀ i j, i ≠ j → p i ⟂ p j) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E) (ty : Fin (Module.finrank ℂ E) → I),
      ∀ i, Submodule.span ℂ (b '' {σ | ty σ = i}) = p i := by
  classical
  have hV : OrthogonalFamily ℂ (fun i => p i) (fun i => (p i).subtypeₗᵢ) :=
    OrthogonalFamily.of_pairwise (fun i j h => horth i j h)
  have hint : DirectSum.IsInternal p :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top p).2 ⟨hV.independent, htop⟩
  let v : ∀ i, OrthonormalBasis (Fin (Module.finrank ℂ (p i))) ℂ (p i) :=
    fun i => stdOrthonormalBasis ℂ (p i)
  let c := hint.collectedOrthonormalBasis hV v
  have hc : ∀ a : (Σ i, Fin (Module.finrank ℂ (p i))), c a = (v a.1 a.2 : E) := by
    intro a
    simp [c, DirectSum.IsInternal.collectedOrthonormalBasis, DirectSum.IsInternal.collectedBasis_coe]
  have hcard : Fintype.card (Σ i, Fin (Module.finrank ℂ (p i))) = Module.finrank ℂ E :=
    (Module.finrank_eq_card_basis c.toBasis).symm
  let e : (Σ i, Fin (Module.finrank ℂ (p i))) ≃ Fin (Module.finrank ℂ E) :=
    Fintype.equivFinOfCardEq hcard
  refine ⟨c.reindex e, fun σ => (e.symm σ).1, fun i => ?_⟩
  have himg : (c.reindex e) '' {σ | (e.symm σ).1 = i}
      = (p i).subtype '' Set.range (v i).toBasis := by
    ext x
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      rw [OrthonormalBasis.reindex_apply, hc]
      simp only [Set.mem_ofPred_eq] at hσ
      generalize e.symm σ = a at hσ
      obtain ⟨j, k⟩ := a
      subst hσ
      exact ⟨v j k, ⟨k, by simp⟩, rfl⟩
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      refine ⟨e ⟨i, k⟩, by simp, ?_⟩
      rw [OrthonormalBasis.reindex_apply, Equiv.symm_apply_apply, hc]
      simp
  rw [himg, ← Submodule.map_span, Module.Basis.span_eq, Submodule.map_top, Submodule.range_subtype]

end GlobalTheory.Mem
