module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseCoverFramesDifferByRationalIsometryStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverComponentEqImpliesBaseComponentEqStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverReadingEqPowMulMovedFrameReadingStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoverDictionaryAdelicElementComponentStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalIsometryMapsFlagDomainFramesStatement
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

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverFrame

theorem comp_over_comp : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ k₂ : C.U₂.Comp, ∃ (k : (T.U j σ).Comp) (γ : GL (Fin D.R.r) D.host.E), (((T.U j σ).X k).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X k₂).Λ : Set _) ∧ (∀ v w, herm ((T.U j σ).X k).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X k₂).Gm v w) ∧ (∀ h, (C.dict₂ h).1 = k₂ → (T.dict j σ h).1 = k) ∧ ∀ (x : Frame (C.U₂.X k₂).Ψ D.R.r) (x' : Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ (C.U₂.X k₂).dom → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k).Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → x' ∈ ((T.U j σ).X k).dom ∧ ∃ t : ℂ, t ≠ 0 ∧ ∀ n : ℕ, ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → rdU C.U₂ f₂ k₂ x = t ^ n * rdU (T.U j σ) f k x' := by
  intro D T hT j hj σ hσ C hC k₂
  obtain ⟨h₀, rfl⟩ := GlobalTheory.T.exists_coverDictionary_adelic_element_component D T hT j hj σ hσ C hC k₂
  obtain ⟨γ, hΛ, hiso, hfr⟩ := GlobalTheory.T.base_cover_frames_differ_by_rational_isometry D T hT j hj σ hσ C hC h₀
  refine ⟨(T.dict j σ h₀).1, γ, hΛ, hiso, fun h hh => GlobalTheory.T.cover_component_eq_implies_base_component_eq D T hT j hj σ hσ C hC h h₀ hh,
    fun x x' hx hxx' => ?_⟩
  have hU := hT.unf j hj σ hσ
  have hU₂ := hC.2.2.2.1
  have hx' : x' ∈ ((T.U j σ).X (T.dict j σ h₀).1).dom :=
    GlobalTheory.T.rationalIsometry_maps_flagDomain_frames _ _ _ _ γ ((hU.2.1 _).1.trans (hU₂.2.1 _).1.symm)
      (fun τ => ((hU.2.1 _).2 τ).trans ((hU₂.2.1 _).2 τ).symm) hiso x x' hx hxx'
  exact ⟨hx', GlobalTheory.T.coverReading_eq_pow_mul_movedFrameReading D T hT j hj σ hσ C hC h₀ γ hΛ hiso hfr x x' hx hx' hxx'⟩

end GlobalTheory.CoverFrame
