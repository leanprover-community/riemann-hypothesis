module

public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RationalTuplesDiscreteCocompactAdelic
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianOneByOneIsScalar
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.FinQ

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_sigma (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨-, -, -, hτ⟩ := h
  let w : InfinitePlace E := Classical.arbitrary _
  apply w.embedding.injective
  rw [hτ, hτ, star_star]

theorem exists_moved (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  by_contra hc
  push_neg at hc
  obtain ⟨-, htc, -, hτ⟩ := h
  let w : InfinitePlace E := Classical.arbitrary _
  have hcx : w.IsComplex := htc.isComplex w
  apply InfinitePlace.not_isReal_iff_isComplex.mpr hcx
  rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
  ext x
  have := hτ w.embedding x
  rw [hc x] at this
  simpa using this.symm

theorem fixed_mem (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (e : E) (he : σ e = e) :
    ∃ t : F, e = algebraMap F E t := by
  apply GlobalTheory.CompanionTheory.SW.HermOne.exists_eq_algebraMap <;> assumption

theorem hE_self_fixed (σ : E →ₐ[F] E) (h : IsCMExt F E σ) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (x : Fin M → E) :
    σ (hE σ J x x) = hE σ J x x := by

  simp only [hE, hform, map_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : σ ((σ : E →+* E) (x j)) = x j := sigma_sigma σ h (x j)
  have h2 : σ (J j i) = J i j := hJ.1 i j
  have h3 : (σ : E →+* E) (x i) = σ (x i) := rfl
  rw [h1, h2, h3]
  ring

end Field

theorem gram_rational_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    (∀ X : Fin 1 → Fin M → E, ∃ t : F, gramE σ J X = fun _ _ => algebraMap F E t) ∧
    (∀ (n : ℕ) (X : Fin n → Fin M → E),
      gramR (AF F) σ J (ratTup (AF F) X) = (gramE σ J X).map (inclR (AF F))) ∧
    ∀ Ω : Set (Fin 1 → Fin M → AF F ⊗[F] E), IsCompact Ω →
      {t : F | ∃ Y ∈ Ω, gramR (AF F) σ J Y = fun _ _ => inclR (AF F) (algebraMap F E t)}.Finite := by
  intro F E _ _ _ _ _ σ hcm M J hJ
  refine ⟨?_, ?_, ?_⟩
  · intro X
    obtain ⟨t, ht⟩ := fixed_mem σ hcm _ (hE_self_fixed σ hcm J hJ (X 0))
    refine ⟨t, ?_⟩
    funext a b
    rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
    exact ht
  · intro n X
    ext a b
    have hs : ∀ e : E, sigR (AF F) σ (inclR (AF F) e) = inclR (AF F) (σ e) := fun e => by
      simp [sigR, inclR]

    simp only [gramR, hR, hform, ratTup, JR, Matrix.map_apply, gramE, hE, map_sum, map_mul, hs]
    rfl
  · intro Ω hΩ
    obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
    have hcont : Continuous (gramR (AF F) σ J : (Fin 1 → Fin M → AF F ⊗[F] E) → _) :=
      (_root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm (AF F)).2.2.2.2.2.2.2.2.2 1 M J
    let φ : (Fin 1 → Fin M → AF F ⊗[F] E) → Fin 1 → Fin 1 → AF F ⊗[F] E :=
      fun Y _ _ => gramR (AF F) σ J Y 0 0
    have hφ : Continuous φ :=
      continuous_pi fun _ => continuous_pi fun _ => hcont.matrix_elem 0 0
    have hfin := (_root_.GlobalTheory.CompanionTheory.SW.CocW.main F E σ hcm 1 1).2.1 _ (hΩ.image hφ)
    let ι : F → Fin 1 → Fin 1 → E := fun t _ _ => algebraMap F E t
    refine Set.Finite.of_injOn (f := ι) ?_ ?_ hfin
    · rintro t ⟨Y, hY, hYt⟩
      refine ⟨Y, hY, ?_⟩
      funext a b
      exact congrFun (congrFun hYt 0) 0
    · intro s _ t _ hst
      exact (algebraMap F E).injective (congrFun (congrFun hst 0) 0)

end GlobalTheory.CompanionTheory.SW.FinQ
