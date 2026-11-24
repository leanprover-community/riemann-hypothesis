module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP Matrix

namespace GlobalTheory.AlgWtHW

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem exists_gq (γ₀ : GL (Fin n) L) (h : γ₀ ∈ GQ0 L n) :
    ∃ γ : GQ L n, (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) := by
  set g := Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) γ₀ with hgdef
  have hg : g ∈ GA L n := by
    show g.val * conjT (conjAL L) g.val = 1
    have e : conjT (conjAL L) g.val =
        (conjT (IsCMField.complexConj L : L →+* L) γ₀.val).map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) := by
      ext i j
      simp [conjT, g, conjAL, Algebra.TensorProduct.map_tmul]
    rw [e]
    have h' : γ₀.val * conjT (IsCMField.complexConj L : L →+* L) γ₀.val = 1 := h
    show γ₀.val.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) * _ = 1
    rw [← Matrix.map_mul, h', Matrix.map_one _ (map_zero _) (map_one _)]
  exact ⟨⟨⟨g, hg⟩, Subgroup.mem_subgroupOf.2 ⟨γ₀, h, rfl⟩⟩, rfl⟩

theorem conj_conj (φ : L →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := by
  ext x; simp

theorem conjugate_ne_self (τ : L →+* ℂ) : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
  IsTotallyComplex.complexEmbedding_not_isReal τ (ComplexEmbedding.isReal_iff.2 h)

theorem isUPt_ratPt (γ₀ : GL (Fin n) L) (h : γ₀ ∈ GQ0 L n) : IsUPt (ratPt γ₀.val) := by
  intro σ
  have h' : γ₀.val * conjT (IsCMField.complexConj L : L →+* L) γ₀.val = 1 := h
  have e : ratPt γ₀.val (ComplexEmbedding.conjugate σ) = (γ₀.val.map (IsCMField.complexConj L : L →+* L)).map σ := by
    ext i j
    simp [ratPt, IsCMField.complexEmbedding_complexConj]
  rw [e]
  have := congrArg (fun M => M.map σ) h'
  simpa [ratPt, conjT, Matrix.map_mul, Matrix.transpose_map] using this

open scoped Classical in
open Classical in
def tauPt (τ : L →+* ℂ) (B : GL (Fin n) ℂ) : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ := fun σ =>
  if σ = τ then B.val else if σ = ComplexEmbedding.conjugate τ then (B⁻¹).valᵀ else 1

theorem evPt_eq_upt (τ : L →+* ℂ) (B : GL (Fin n) ℂ) :
    Formalism.L2.NG.evPt τ B = upt (tauPt τ B) := by
  funext p
  simp only [Formalism.L2.NG.evPt, upt, tauPt]
  split_ifs <;> simp [Matrix.one_apply, *]

theorem isUPt_tauPt (τ : L →+* ℂ) (B : GL (Fin n) ℂ) : IsUPt (tauPt τ B) := by
  intro σ
  have hne := conjugate_ne_self τ
  by_cases h1 : σ = τ
  · subst h1
    simp [tauPt, hne, Matrix.transpose_transpose]
  · by_cases h2 : σ = ComplexEmbedding.conjugate τ
    · subst h2
      simp only [tauPt, if_neg h1, conj_conj, if_true]
      rw [← Matrix.transpose_transpose (B.val), ← Matrix.transpose_mul, Matrix.transpose_transpose,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]
    · have h3 : ComplexEmbedding.conjugate σ ≠ τ := fun e => h2 (by rw [← e, conj_conj])
      have h4 : ComplexEmbedding.conjugate σ ≠ ComplexEmbedding.conjugate τ := fun e => h1 (by
        simpa using congrArg ComplexEmbedding.conjugate e)
      simp [tauPt, h1, h2, h3, h4]

end GlobalTheory.AlgWtHW
