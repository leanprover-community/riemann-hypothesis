module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeEmbeddingLiftDatumHermitianSpaceStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMemberDictionaryContextGoodEmbeddingStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniformisationDictionaryCharacterLawsStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniformisationWithComponentAtEveryEmbeddinStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

namespace GlobalTheory.Member

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_iotaAll (Q : Par D) (hQ : Q.Pins) (j : ℕ) :
    ∃ ι₀ : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E), InR D j → ∀ hr : (D.sp.W j).rank = D.R.r,
      IotaOK (Q.Dw j) (D.sp.W j) (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀) := by
  by_cases hj : InR D j
  · obtain ⟨⟨ι, hι⟩, -⟩ := GlobalTheory.T.exists_latticeEmbedding_liftDatum_hermitianSpace D Q hQ j hj
    refine ⟨LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (D.sp.W_rank j hj.1 hj.2).symm) ∘ₗ ι,
      fun _ hr => ?_⟩
    have e : LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ
        (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (D.sp.W_rank j hj.1 hj.2).symm) ∘ₗ ι) = ι := by
      ext x i
      rfl
    rw [e]
    exact hι
  · exact ⟨0, fun h => absurd h hj⟩

theorem exists_pkgAll (Q : Par D) (hQ : Q.Pins) (hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) (j : ℕ)
    (σ : Q.c.F →+* ℂ) (ι₀ : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E))
    (hι : InR D j → ∀ hr : (D.sp.W j).rank = D.R.r,
      IotaOK (Q.Dw j) (D.sp.W j) (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀))
    (Kf : Subgroup (GA D (D.sp.W j))) (hK : IsLevelK (D.sp.W j) Q.l.M Kf) (χ : (AE D)ˣ →* Circle)
    (hχ : InR D j → GoodEmb Q.c σ → IsHeckeChar D χ ∧ ∀ a, χ (idF D a) = 1) :
    ∃ (U : Unf (Q.Xo j) Q.c σ D.R.r) (dict : GA D (D.sp.W j) → Σ k, Frame (U.X k).Ψ D.R.r)
      (mu : GA D (D.sp.W j) → ℂ) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ),
      ∀ hj : InR D j, GoodEmb Q.c σ → (∀ k, (U.X k).p0 = (Q.Dw j).q) ∧
        PkgLaws (D.sp.W j) (D.sp.W_rank j hj.1 hj.2)
          (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (D.sp.W_rank j hj.1 hj.2)) ∘ₗ ι₀) Kf χ U dict mu x₀ := by
  by_cases h : InR D j ∧ GoodEmb Q.c σ
  · obtain ⟨hj, hσ⟩ := h
    obtain ⟨⟨C, hC, hCι⟩, -⟩ := GlobalTheory.T.exists_memberDictionaryContext_goodEmbedding D Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c σ (D.sp.W j) D.R.r
      (D.sp.W_rank j hj.1 hj.2) _ (hι hj (D.sp.W_rank j hj.1 hj.2)) (hpq j) hQ.2.1.2 hσ
    obtain ⟨un, dict, mu, -, -, hP⟩ := GlobalTheory.T.exists_uniformisation_dictionary_character_laws D Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c σ (D.sp.W j) D.R.r C hC Kf hK χ
      (hχ hj hσ).1 (hχ hj hσ).2
    rw [hCι] at hP
    exact ⟨C.unf un, dict, mu, C.x₀, fun _ _ => ⟨fun k => (hC.base.type k).1, hP⟩⟩
  · obtain ⟨U, ⟨k⟩⟩ := GlobalTheory.T.exists_uniformisation_with_component_at_every_embedding D Q hQ hpq j σ
    exact ⟨U, fun _ => ⟨k, fun _ _ _ => 0⟩, fun _ => 1, fun _ => 1, fun hj hσ => absurd ⟨hj, hσ⟩ h⟩

end GlobalTheory.Member
