module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto

private theorem continuous_leviProj_hpgIncl (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) (b : Bool) :
    Continuous (fun h : HPG k i t => (leviProj k (ePG i t) (hpgIncl k i t h)) b) := by
  have h0 : Continuous (fun h : HPG k i t =>
      (((h : Mir k (i + t)) : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hv : Continuous (fun h : HPG k i t =>
      ((leviProj k (ePG i t) (hpgIncl k i t h)) b : Matrix (Two (Fin (i + 1)) (Fin t) b) (Two (Fin (i + 1)) (Fin t) b) k)) :=
    (h0.matrix_submatrix (fun j => (ePG i t) ⟨b, j⟩) (fun j => (ePG i t) ⟨b, j⟩)).congr (fun _ => rfl)
  rw [Units.continuous_iff]
  refine ⟨hv, ?_⟩
  have hinv : Continuous (fun h : HPG k i t =>
      ((leviProj k (ePG i t) (hpgIncl k i t h⁻¹)) b : Matrix (Two (Fin (i + 1)) (Fin t) b) (Two (Fin (i + 1)) (Fin t) b) k)) :=
    hv.comp continuous_inv
  refine hinv.congr (fun h => ?_)
  simp only [map_inv, Pi.inv_apply]

theorem continuous_pgProj (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) : Continuous (pgProj k i t) := by
  have h1 : Continuous (fun h : HPG k i t => (pgProj k i t h).1) :=
    continuous_induced_rng.2 ((continuous_leviProj_hpgIncl k i t false).congr (fun _ => rfl))
  have h2 : Continuous (fun h : HPG k i t => (pgProj k i t h).2) :=
    (continuous_leviProj_hpgIncl k i t true).congr (fun _ => rfl)
  exact (h1.prodMk h2).congr (fun _ => rfl)

theorem isSmooth_sigX {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {i t : ℕ} (τ : MRep k (i + 1)) (σ : GRep k (t + 1))
    (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) : IsSmooth (sigX τ σ) := by
  have hd : ∀ (n : ℕ) (s : ℂ), IsSmoothChar (detChar (Fin n) (absPow k s)) :=
    fun n s => IsSmoothChar.detChar (isSmoothChar_of_isUnram (isUnram_absPow k s))
  have h1 : IsSmooth (mtw τ (↑(t + 1) / 2)).ρ := by
    refine isSmooth_twist hτ ?_
    unfold dpowM dpow
    unfold IsSmoothChar
    rw [← MonoidHom.comap_ker]
    exact IsOpen.preimage continuous_subtype_val (hd _ _)
  have h2 : IsSmooth (σ.tw (-↑(i + 1 + 1) / 2)).ρ := by
    unfold GRep.tw
    exact isSmooth_twist hσ (by unfold dpow; exact hd _ _)
  intro v
  exact (isSmooth_extTensor h1 h2 v).preimage (continuous_pgProj k (i + 1) (t + 1))

theorem sigX_fix : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (w : τ.V ⊗[ℂ] σ.V),
  ∃ O ∈ nhds (1 : Mir k ((i + 1) + t + 1)), ∀ h : HPG k (i + 1) (t + 1), ((h : Mir k ((i + 1) + (t + 1))) ∈ O) → sigX τ σ h w = w := by
  intro k _ _ _ _ i t τ σ hτ hσ w
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.1 (isSmooth_sigX τ σ hτ hσ w)
  have h1 : (1 : HPG k (i + 1) (t + 1)) ∈ Subtype.val ⁻¹' O := by
    rw [hOeq]
    simp
  refine ⟨O, hO.mem_nhds h1, fun h hh => ?_⟩
  have hh' : h ∈ Subtype.val ⁻¹' O := hh
  rw [hOeq] at hh'
  exact hh'

end GlobalTheory.CompanionTheory.BZPhiPG.Onto
