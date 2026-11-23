module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StabProper

private lemma sum_mul_conj_eq_conj_dotProduct {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    ∑ a, ∑ b, x a * conj (G b a) * conj (y b) = conj (y ⬝ᵥ (G *ᵥ star x)) := by

  simp only [dotProduct, mulVec, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_conj]
  ring

theorem unitary_iff_form {n : ℕ} (G g : Matrix (Fin n) (Fin n) ℂ) :
    gᴴ * G * g = G ↔ ∀ v w : Fin n → ℂ,
      ∑ a, ∑ b, (g.map conj *ᵥ v) a * conj (G b a) * conj ((g.map conj *ᵥ w) b) =
        ∑ a, ∑ b, v a * conj (G b a) * conj (w b) := by
  have h1 : ∀ v : Fin n → ℂ, star (g.map conj *ᵥ v) = g *ᵥ star v := by
    intro v; ext i
    simp [mulVec, dotProduct]
  have key : ∀ v w : Fin n → ℂ, ∑ a, ∑ b, (g.map conj *ᵥ v) a * conj (G b a) * conj ((g.map conj *ᵥ w) b) =
      conj (w ⬝ᵥ ((gᴴ * G * g) *ᵥ star v)) := by
    intro v w
    rw [sum_mul_conj_eq_conj_dotProduct, h1]
    congr 1
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec w gᴴ]
    congr 1
    ext j
    simp [vecMul, mulVec, dotProduct, conjTranspose_apply, mul_comm]
  constructor
  · intro h v w
    rw [key, h, sum_mul_conj_eq_conj_dotProduct]
  · intro h
    ext i j
    have hs : ∀ k : Fin n, star (Pi.single k 1 : Fin n → ℂ) = Pi.single k 1 := by
      intro k; ext l; by_cases hl : l = k <;> simp [hl]
    have := h (Pi.single j 1) (Pi.single i 1)
    rw [key, sum_mul_conj_eq_conj_dotProduct, hs] at this
    have := (starRingEnd ℂ).injective this
    simpa [mulVec, dotProduct, Pi.single_apply] using this

variable {D : D7}

theorem compAt_eq (θ : InfFam D) (τ : D.what₂.Tau) {m n : ℕ} (w : Mx D m n) :
    compAt θ τ w = w.map ((θ τ).comp (infPart D)) := rfl

theorem hermC_eq {S T : HSp D} (C : Ctx S T) (σ : C.X.Ψ) (v w : Fin T.rank → ℂ) :
    hermC σ.1 C.X.Gm v w = ∑ a, ∑ b, v a * conj (gramAt D T (C.m.e.symm σ) b a) * conj (w b) := by
  unfold hermC gramAt
  have he := C.m.e_emb (C.m.e.symm σ)
  rw [Equiv.apply_symm_apply] at he
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [C.m.gT, he]
  simp [NumberField.ComplexEmbedding.conjugate_coe_eq]

end GlobalTheory.StabProper

end
