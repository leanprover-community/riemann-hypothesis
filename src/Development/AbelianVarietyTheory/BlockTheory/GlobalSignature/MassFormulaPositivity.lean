module

public import Formalism.LocalRingCardinality.DataSpaces
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.MassFormulaPositivity

open NumberField Formalism.BasicNotions


open scoped ComplexOrder in
theorem posDef_of_hasSignature {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ} {p : ℕ}
    (h : Formalism.UG.HasSignature J p 0) : J.PosDef := by
  obtain ⟨e, P, hP⟩ := h
  have hJ : Formalism.UG.Jpq p 0 = 1 := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [Formalism.UG.Jpq, Matrix.one_apply]
      · exact j.elim0
    · exact i.elim0
  have hc : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin 0) (Fin p ⊕ Fin 0) ℂ) =
      star (P : Matrix (Fin p ⊕ Fin 0) (Fin p ⊕ Fin 0) ℂ) := by
    ext i j; rfl
  rw [hJ, hc] at hP
  have h1 : (J.reindex e e).PosDef := by
    rw [← Matrix.IsUnit.posDef_star_left_conjugate_iff (Units.isUnit P), hP]
    exact Matrix.PosDef.one
  have h2 := h1.submatrix (e := e) e.injective
  simpa using h2

theorem trace_pos {E : Type} [Field E] [NumberField E] [StarRing E]
    (hst : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a))
    (W : HSpace E) (hs : W.SigOK) {p : ℕ} (hp : ∀ τ : E →+* ℂ, W.sig τ = (p, 0))
    (x : W.V) (hx : x ≠ 0) : 0 < Algebra.trace ℚ E (W.hT x x) := by
  classical
  have hloc : ∀ τ : E →+* ℂ, 0 < (τ (W.hT x x)).re := by
    intro τ
    have h0 := hs τ
    rw [hp τ] at h0
    have hpd := posDef_of_hasSignature h0
    have hv : (fun i => τ (W.frame.repr x i)) ≠ 0 := by
      intro h
      apply hx
      apply W.frame.repr.injective
      ext i
      simpa using congrFun h i
    have h1 := hpd.re_dotProduct_pos hv
    have h2 : τ (W.hT x x) = star (fun i => τ (W.frame.repr x i)) ⬝ᵥ
        (W.gram.map τ).mulVec (fun i => τ (W.frame.repr x i)) := by
      conv_lhs => rw [← W.frame.sum_repr x]

      simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, map_mul, RingHom.id_apply, starRingEnd_apply, hst, dotProduct, Matrix.mulVec,
      Matrix.map_apply, HSpace.gram, Pi.star_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h2]
    exact h1
  have ht := trace_eq_sum_embeddings ℂ (K := ℚ) (L := E) (x := W.hT x x)
  have hre := congrArg Complex.re ht
  rw [Complex.re_sum] at hre
  have hpos : 0 < ∑ σ : E →ₐ[ℚ] ℂ, (σ (W.hT x x)).re :=
    Finset.sum_pos (fun σ _ => hloc (σ : E →+* ℂ)) ⟨IsAlgClosed.lift, Finset.mem_univ _⟩
  rw [← hre] at hpos
  simpa using hpos

end GlobalTheory.IndefiniteRowSideFullHecke.MassFormulaPositivity
