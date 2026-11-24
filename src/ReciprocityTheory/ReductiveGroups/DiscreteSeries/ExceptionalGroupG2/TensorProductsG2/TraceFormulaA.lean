module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaA
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.CoefOfEmb
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.MultOne
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigLamMemLpOfNe
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.ClosGenStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.MultOneA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.RorthFunctionalEqZero
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.CoefEmbed

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

section ClRep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {ε : Fin n → Bool} {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

theorem tfClRep_isURepOn (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) :
    IsURepOn (UJset ε) (tfClRep σ (closGen E V)) := by
  have hst := closGen_stable hgap hσ hD hV hc hVK
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
    show inUJ ε 1
    simp [inUJ]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · refine ContinuousLinearMap.ext fun x => Subtype.ext ?_
    rw [tfClRep_coe σ _ (hst 1 h1) x, hσ.1.1]
    rfl
  · intro a ha b hb
    refine ContinuousLinearMap.ext fun x => Subtype.ext ?_
    rw [ContinuousLinearMap.comp_apply, tfClRep_coe σ _ (hst _ (mul_mem_unitaryJ ha hb)) x,
      tfClRep_coe σ _ (hst a ha), tfClRep_coe σ _ (hst b hb), hσ.1.2 a ha b hb, ContinuousLinearMap.comp_apply]
  · intro g hg x
    have h := hσ.2.1 g hg (x : H)
    rw [← tfClRep_coe σ _ (hst g hg) x] at h
    simpa using h
  · intro v
    exact (closGen E V).orthogonalProjectionOnto.continuous.comp_continuousOn (hσ.2.2 (v : H))

theorem tfClRep_irred (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) :
    Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) (tfClRep σ (closGen E V)) := by
  have hst := closGen_stable hgap hσ hD hV hc hVK
  intro S hSc hSG
  have hinj : Function.Injective (closGen E V).subtype := Subtype.val_injective
  have hcl : IsClosed ((S.map (closGen E V).subtype : Submodule ℂ H) : Set H) := by
    have h := (Submodule.isClosed_topologicalClosure _).isClosedEmbedding_subtypeVal.isClosedMap
      (S : Set (closGen E V)) hSc
    rw [Submodule.map_coe]
    exact h
  have hle : S.map (closGen E V).subtype ≤ closGen E V := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hSt : ∀ g ∈ UJset ε, ∀ x ∈ S.map (closGen E V).subtype, σ g x ∈ S.map (closGen E V).subtype := by
    rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨tfClRep σ (closGen E V) g x, hSG g (by rw [mir_UJset_eq]; exact hg) x hx, tfClRep_coe σ _ (hst g hg) x⟩
  rcases rigid_irred hgap hσ hD hV hc hVK _ hle hcl hSt with h | h
  · left
    exact Submodule.map_injective_of_injective hinj (h.trans (Submodule.map_bot _).symm)
  · right
    apply Submodule.map_injective_of_injective hinj
    rw [h, Submodule.map_top, Submodule.range_subtype]

theorem tfClRep_fdeg (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hSq : Formalism.MainNotions.S.IsSqIntOn ε (tfClRep σ (closGen E V))) :
    ∃ d : ℝ, Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) (tfClRep σ (closGen E V)) d := by
  have hU := tfClRep_isURepOn hgap hσ hD hV hc hVK
  have hU' : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) (tfClRep σ (closGen E V)) := by
    rw [mir_UJset_eq]; exact hU
  exact Formalism.MainNotions.BridgeCSchur.schur_UJ _ (tfClRep_nontrivial hV) hU' (tfClRep_irred hgap hσ hD hV hc hVK) hSq

theorem tfClRep_schur (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) (tfClRep σ (closGen E V)) d)
    {u v u' v' : H} (hu : u ∈ closGen E V) (hv : v ∈ closGen E V) (hu' : u' ∈ closGen E V) (hv' : v' ∈ closGen E V) :
    Integrable (fun g : Formalism.REAL.UJ ε => inner ℂ u (σ (Formalism.MainNotions.S.umat g) v) * star (inner ℂ u' (σ (Formalism.MainNotions.S.umat g) v')))
      (Formalism.REAL.muG ε) ∧
    ∫ g, inner ℂ u (σ (Formalism.MainNotions.S.umat g) v) * star (inner ℂ u' (σ (Formalism.MainNotions.S.umat g) v')) ∂(Formalism.REAL.muG ε) =
      inner ℂ v' v * inner ℂ u u' / (d : ℂ) := by
  have hst := closGen_stable hgap hσ hD hV hc hVK
  obtain ⟨-, h⟩ := hd
  obtain ⟨h1, h2⟩ := h ⟨v, hv⟩ ⟨u, hu⟩ ⟨v', hv'⟩ ⟨u', hu'⟩
  have e : ∀ (x y : closGen E V) (g : Formalism.REAL.UJ ε),
      Formalism.MainNotions.S.coefOn (tfClRep σ (closGen E V)) x y g = inner ℂ (y : H) (σ (Formalism.MainNotions.S.umat g) x) := by
    intro x y g
    simp only [Formalism.MainNotions.S.coefOn]
    rw [Submodule.coe_inner, tfClRep_coe σ _ (hst _ (umat_mem_UJset ε g))]
  simp only [e] at h1 h2
  refine ⟨h1, ?_⟩
  rw [h2, Submodule.coe_inner, Submodule.coe_inner]

end ClRep

end ReciprocityTheory.ChartRestriction.DS.G2
