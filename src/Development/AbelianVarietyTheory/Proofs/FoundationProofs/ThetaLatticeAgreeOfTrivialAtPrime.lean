module

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RelIndexNeZeroOfMoves
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleStrongApproxModAdelicIdeal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaLatticePointMemThetaLatticeOfAdelicStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRationalPointOfMemMovedThetaLatticeStatement
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

noncomputable section

namespace GlobalTheory.NormSum.LocAgree

theorem exists_int_mul (D : D7) {N : ℕ} (q : ℕ) (k : GA D N) (h : TrivAt D q (k : GL (Fin N) (AE D))) :
    ∃ s : ℕ, Nat.Coprime s q ∧
      (∀ i j, (s : AE D) * ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D) ∧
      ∀ i j, (s : AE D) * (((k : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) :
        Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
  apply GlobalTheory.InertParity.LengthSign.exists_int_mul <;> assumption

theorem pt_nsmul (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (m : ℕ)
    (z : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ ((m : D.host.E) • z) = m • pt D (tor0 D cc δ) δ z := by
  funext τ i j
  show δ * embT D τ ((m : D.host.E) * z i j) = m • (δ * embT D τ (z i j))
  rw [map_mul, map_natCast, nsmul_eq_mul]
  ring

theorem matrix_move {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) {N N' : ℕ} (g₁ g₂ : GL (Fin N) A)
    (g₁' g₂' : GL (Fin N') A) (s s' : ℕ) (z : Matrix (Fin N') (Fin N) R) :
    ((g₂'⁻¹ : GL (Fin N') A) : Matrix (Fin N') (Fin N') A) * (((s * s' : ℕ) : R) • z).map f *
      (g₂ : Matrix (Fin N) (Fin N) A) =
      ((s' : A) • ((g₂'⁻¹ * g₁' : GL (Fin N') A) : Matrix (Fin N') (Fin N') A)) *
      (((g₁'⁻¹ : GL (Fin N') A) : Matrix (Fin N') (Fin N') A) * z.map f * (g₁ : Matrix (Fin N) (Fin N) A)) *
      ((s : A) • ((g₁⁻¹ * g₂ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A)) := by
  have e1 : (((s * s' : ℕ) : R) • z).map f = ((s : A) * (s' : A)) • z.map f := by
    ext i j
    simp
  rw [e1]
  simp only [Units.val_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (g₁ : Matrix (Fin N) (Fin N) A), Units.mul_inv, Matrix.one_mul,
    ← Matrix.mul_assoc (g₁' : Matrix (Fin N') (Fin N') A), Units.mul_inv, Matrix.one_mul]

theorem smul_mem_La (D : D7) (hG : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : cc ≠ ⊥) {N N' : ℕ}
    (g₁ g₂ : GA D N) (g₁' g₂' : GA D N')
    {L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h₁ : Moves D (g₁ : GL (Fin N) (AE D)) L₁) (h₁' : Moves D (g₁' : GL (Fin N') (AE D)) L₁')
    (h₂ : Moves D (g₂ : GL (Fin N) (AE D)) L₂) (h₂' : Moves D (g₂' : GL (Fin N') (AE D)) L₂')
    (s s' : ℕ)
    (hs : ∀ i j, (s : AE D) * (((g₁ : GL (Fin N) (AE D))⁻¹ * (g₂ : GL (Fin N) (AE D)) : GL (Fin N) (AE D)) :
      Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D)
    (hs' : ∀ i j, (s' : AE D) * (((g₂' : GL (Fin N') (AE D))⁻¹ * (g₁' : GL (Fin N') (AE D)) : GL (Fin N') (AE D)) :
      Matrix (Fin N') (Fin N') (AE D)) i j ∈ OhE D)
    (x : VC D N N') (hx : x ∈ La D (tor0 D cc δ) L₁ L₁') : (s * s') • x ∈ La D (tor0 D cc δ) L₂ L₂' := by
  obtain ⟨z, rfl, hz⟩ := GlobalTheory.T.exists_rationalPoint_of_mem_movedThetaLattice D hG cc δ hc N N' g₁ g₁' L₁ L₁' h₁ h₁' x hx
  rw [← pt_nsmul]
  refine GlobalTheory.T.cmThetaLatticePoint_mem_thetaLattice_of_adelic D hG cc δ hc N N' g₂ g₂' L₂ L₂' h₂ h₂' _ ?_
  have hI := (GlobalTheory.AdelicApprox.approx_mod_ideal D cc hc).2.2
  intro i j
  rw [matrix_move (inc D) (g₁ : GL (Fin N) (AE D)) _ (g₁' : GL (Fin N') (AE D)), Matrix.mul_apply]
  refine sum_mem fun l _ => ?_
  rw [mul_comm]
  refine hI _ (hs l j) _ ?_
  rw [Matrix.mul_apply]
  exact sum_mem fun r _ => hI _ (hs' i r) _ (hz r l)

end GlobalTheory.NormSum.LocAgree


open GlobalTheory.NormSum.LocAgree in
theorem GlobalTheory.NormSum.La_agree_of_trivAt : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → ∀ (N N' q : ℕ) (h k : GA D N) (h' k' : GA D N') (L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TrivAt D q (k : GL (Fin N) (AE D)) → TrivAt D q (k' : GL (Fin N') (AE D)) → Moves D (h : GL (Fin N) (AE D)) L₁ → Moves D (h' : GL (Fin N') (AE D)) L₁' → Moves D ((h * k : GA D N) : GL (Fin N) (AE D)) L₂ → Moves D ((h' * k' : GA D N') : GL (Fin N') (AE D)) L₂' → (∀ x ∈ La D (tor0 D cc δ) L₁ L₁', ∃ m : ℕ, Nat.Coprime m q ∧ m • x ∈ La D (tor0 D cc δ) L₂ L₂') ∧ (∀ x ∈ La D (tor0 D cc δ) L₂ L₂', ∃ m : ℕ, Nat.Coprime m q ∧ m • x ∈ La D (tor0 D cc δ) L₁ L₁') := by
  intro D hG cc δ hc N N' q h k h' k' L₁ L₂ L₁' L₂' hk hk' h₁ h₁' h₂ h₂'
  obtain ⟨s, hsq, hs, hsi⟩ := exists_int_mul D q k hk
  obtain ⟨s', hsq', hs', hsi'⟩ := exists_int_mul D q k' hk'
  refine ⟨fun x hx => ⟨s * s', Nat.Coprime.mul_left hsq hsq', ?_⟩,
    fun x hx => ⟨s * s', Nat.Coprime.mul_left hsq hsq', ?_⟩⟩
  · refine smul_mem_La D hG cc δ hc h (h * k) h' (h' * k') h₁ h₁' h₂ h₂' s s' ?_ ?_ x hx
    · rw [Subgroup.coe_mul, inv_mul_cancel_left]; exact hs
    · rw [Subgroup.coe_mul, mul_inv_rev, inv_mul_cancel_right]; exact hsi'
  · refine smul_mem_La D hG cc δ hc (h * k) h (h' * k') h' h₂ h₂' h₁ h₁' s s' ?_ ?_ x hx
    · rw [Subgroup.coe_mul, mul_inv_rev, inv_mul_cancel_right]; exact hsi
    · rw [Subgroup.coe_mul, inv_mul_cancel_left]; exact hs'
