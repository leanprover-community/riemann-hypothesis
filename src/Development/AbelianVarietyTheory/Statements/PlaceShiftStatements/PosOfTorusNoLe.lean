import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
import Development.AbelianVarietyTheory.Definitions.UpperBounds.SingleMemIntVec
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf

noncomputable section

namespace GlobalTheory.UCls.Model

open NumberField Matrix GlobalTheory.AdLat ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Inst
open GlobalTheory.Up.Definite

section Field

theorem exists_half {E : Type} [Field E] [NumberField E] {x : E} {n m : ℕ} (hm : n + 1 = 4 * m) (hs : x ^ 2 = -(n : E)) :
    ∃ y w : 𝓞 E, y ^ 2 = -(n : 𝓞 E) ∧ 2 * w = 1 + y := by
  have hi : IsIntegral ℤ x :=
    ⟨Polynomial.X ^ 2 + Polynomial.C (n : ℤ), by monicity!, by simp [Polynomial.eval₂_add, hs]⟩
  have hw : IsIntegral ℤ ((1 + x) / 2) := by
    set c : E := (1 + x) / 2
    have hc : c ^ 2 - c + (m : E) = 0 := by
      have e : (n : E) + 1 = 4 * (m : E) := by exact_mod_cast hm
      simp only [c]
      linear_combination (1 / 4 : E) * hs - (1 / 4 : E) * e
    exact ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), by monicity!, by
      simp [Polynomial.eval₂_sub, Polynomial.eval₂_add, hc]⟩
  obtain ⟨y, hy⟩ : ∃ y : 𝓞 E, algebraMap _ E y = x := ⟨⟨x, hi⟩, rfl⟩
  obtain ⟨w, hw0⟩ : ∃ w : 𝓞 E, algebraMap _ E w = (1 + x) / 2 := ⟨⟨_, hw⟩, rfl⟩
  refine ⟨y, w, ?_, ?_⟩
  · apply IsFractionRing.injective (𝓞 E) E
    rw [map_pow, map_neg, map_natCast, hy]
    exact hs
  · apply IsFractionRing.injective (𝓞 E) E
    rw [map_mul, map_add, map_one, map_ofNat, hy, hw0]
    field_simp

theorem exists_field : ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E),
    Unr E ∧ ∀ u : E, IsOfFinOrder u → u = 1 ∨ u = -1 := by
  have hh : Formalism.FrobeniusOrbits.HostHyp 11 7 := ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  obtain ⟨L, _, _, ζ, a, b, h⟩ := Formalism.TwoAdicCyclotomicDecomposition.layerExists (0 + 2) 11 7
  have := Formalism.FrobeniusOrbits.isCMField_hostE hh.toHypOdd h
  refine ⟨Formalism.FrobeniusOrbits.hostE ζ a b, inferInstance, inferInstance, inferInstance, ?_, fun u hu => ?_⟩
  · have ha : Formalism.FrobeniusOrbits.aE ζ a b ^ 2 = -((11 : ℕ) : Formalism.FrobeniusOrbits.hostE ζ a b) := by
      apply Subtype.ext
      exact h.2.1
    have hb : Formalism.FrobeniusOrbits.bE ζ a b ^ 2 = -((7 : ℕ) : Formalism.FrobeniusOrbits.hostE ζ a b) := by
      apply Subtype.ext
      exact h.2.2.1
    obtain ⟨y₁, w₁, h1, h2⟩ := exists_half (m := 3) (by norm_num) ha
    obtain ⟨y₂, w₂, h3, h4⟩ := exists_half (m := 2) (by norm_num) hb
    exact GlobalTheory.HostModel.unramified_of_sqrt (by norm_num : Nat.Coprime 11 7) h1 h3 h2 h4
  · exact Formalism.FrobeniusOrbits.hostMu 0 11 7 hh (by norm_num) L ζ a b h u (isOfFinOrder_iff_pow_eq_one.1 hu)

end Field

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem selfDual_one : SelfDualLat (1 : Matrix (Fin r) (Fin r) E) (intVec E r) := by
  refine ⟨(data E r).Gm_herm, by simp, (data E r).Λ_fg, (data E r).Λ_span, fun x => ⟨fun h => ?_, fun hx y hy => ?_⟩⟩
  · rw [mem_intVec]
    intro a
    have := h _ (single_mem_intVec a)
    rw [Up.Definite.herm_one, Finset.sum_eq_single a] at this
    · simpa [cc_one] using this
    · intro b _ hb; simp [hb, cc_zero]
    · simp
  · rw [mem_intVec] at hx hy
    rw [Up.Definite.herm_one]
    exact IsIntegral.sum _ fun a _ => (hx a).mul (isIntegral_cc (hy a))

theorem pos_one (τ : E →+* ℂ) (x : Fin r → E) (hx : x ≠ 0) :
    0 < (τ (herm (1 : Matrix (Fin r) (Fin r) E) x x)).re := by
  rw [map_herm_one_self, Complex.ofReal_re]
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hx
  refine Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨a, Finset.mem_univ _, ?_⟩
  have : τ (x a) ≠ 0 := by simpa using ha
  positivity







end GlobalTheory.UCls.Model
