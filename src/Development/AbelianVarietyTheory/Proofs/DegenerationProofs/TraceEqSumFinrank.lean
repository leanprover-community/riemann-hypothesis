module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceEqFinrankMulSum
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.Ex.Arch

variable {E : Type} [Field E] [NumberField E]

theorem exists_types (m : (E →+* ℂ) → ℕ) : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)),
    (∀ φ, Nat.card {i // ty i = φ} = m φ) ∧ ∀ a : E, ∑ i, ty i a = ∑ φ : E →+* ℂ, (m φ : ℂ) * φ a := by
  classical
  let e := (Fintype.equivFin (Σ φ : E →+* ℂ, Fin (m φ))).symm
  refine ⟨_, fun i => (e i).1, fun φ => ?_, fun a => ?_⟩
  · rw [Nat.card_congr (e.subtypeEquiv (q := fun k => k.1 = φ) fun _ => Iff.rfl),
      Nat.card_congr (Equiv.sigmaSubtype φ)]
    simp
  · rw [e.sum_comp fun k => k.1 a, Fintype.sum_sigma]
    simp

theorem trace_eq_sum_finrank {g : ℕ} (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (a : 𝓞 E) :
    LinearMap.trace ℂ _ (ρ a) = ∑ φ : E →+* ℂ,
      (Module.finrank ℂ (EigenSplit.eigenSub ρ (φ.comp (algebraMap (𝓞 E) E))) : ℂ) * φ (a : E) := by
  obtain ⟨g', ty, hc, hs⟩ :=
    exists_types fun φ : E →+* ℂ => Module.finrank ℂ (EigenSplit.eigenSub ρ (φ.comp (algebraMap (𝓞 E) E)))
  obtain ⟨h, hh⟩ := PointUnif.exists_equiv_of_finrank_eq (PointUnif.isSplitting_embeddings (E := E))
    (PointUnif.diagRep ty) ρ fun φ => by rw [PointUnif.finrank_eigenSub_diagRep, hc]
  have h1 : ρ a = h.conj (PointUnif.diagRep ty a) := LinearMap.ext fun v => by simp [LinearEquiv.conj_apply, hh]
  have h2 : PointUnif.diagRep ty a = Matrix.toLin' (Matrix.diagonal fun i => ty i (a : E)) :=
    LinearMap.ext fun z => funext fun i => by simp [PointUnif.diagRep_apply, Matrix.mulVec_diagonal]
  rw [h1, LinearMap.trace_conj', h2, ← hs]
  simp

theorem typeSt : TypeSt := by
  intro E _ _ _ H D
  let _ := H.starRing
  intro B hB
  classical
  obtain ⟨g, ty, hc, hs⟩ := exists_types fun φ : E →+* ℂ => if φ (H.rt : E) = H.rt0 then D.p else D.q
  have hbar : ∀ a : 𝓞 E, ∑ τ : E →+* ℂ, τ (H.bar a : E) = ∑ τ : E →+* ℂ, τ (a : E) := fun a => by
    refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro τ _; exact Finset.mem_univ _
    · intro τ _; exact Finset.mem_univ _
    · intro τ _; ext x; simp
    · intro τ _; ext x; simp
    · intro τ _
      rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]
  have := HomTrace.finite_hom B.X
  obtain ⟨h, hh⟩ := PeriodNonempty.exists_diag B.actV ty fun a => by
    let f : (B.X →+ ℂ) →ₗ[ℂ] (B.X →+ ℂ) := LinearMap.fst ℂ _ _ ∘ₗ B.actV a ∘ₗ LinearMap.inl ℂ _ _
    have h1 : B.actV a = f.prodMap (B.F a) := LinearMap.ext fun v => rfl
    rw [h1, LinearMap.trace_prodMap', HomTrace.trace_eq_finrank_mul_sum E B.X (H.bar a) f fun _ _ => rfl, hbar,
      trace_eq_sum_finrank, hs, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun φ _ => ?_
    have h2 : Module.finrank ℂ (EigenSplit.eigenSub B.F (φ.comp (algebraMap (𝓞 E) E))) + Module.finrank (𝓞 E) B.X =
        if φ (H.rt : E) = H.rt0 then D.p else D.q := by
      have h3 := hB (φ.comp (algebraMap (𝓞 E) E))
      by_cases hφ : φ (H.rt : E) = H.rt0
      · rw [if_pos hφ]; exact h3.trans (if_pos hφ)
      · rw [if_neg hφ]; exact h3.trans (if_neg hφ)
    rw [← h2]
    push_cast
    ring
  exact ⟨g, ty, h, fun φ => ⟨fun hφ => (hc φ).trans (if_pos hφ), fun hφ => (hc φ).trans (if_neg hφ)⟩, hh⟩

end GlobalTheory.Ex.Arch

end
