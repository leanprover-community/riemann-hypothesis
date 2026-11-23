module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeftMulMatrixTransfer
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix Polynomial
open GlobalTheory.ClassParam (krylov krylov_map exists_cyclic_field)

namespace GlobalTheory.SemilocalConj

theorem exists_cyclic_of_finite_maximal {R : Type} [CommRing R]
    (hfin : Set.Finite {I : Ideal R | I.IsMaximal}) {r : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (hs : g.charpoly.Separable) : ∃ v, IsUnit (krylov g v).det := by
  classical
  haveI : Finite (MaximalSpectrum R) := by
    haveI := hfin.to_subtype
    exact Finite.of_injective (fun m : MaximalSpectrum R =>
      (⟨m.asIdeal, m.isMaximal⟩ : {I : Ideal R | I.IsMaximal}))
      (fun a b h => MaximalSpectrum.ext (congrArg Subtype.val h))
  have hloc : ∀ m : MaximalSpectrum R, ∃ v : Fin r → R ⧸ m.asIdeal,
      (krylov (g.map (Ideal.Quotient.mk m.asIdeal)) v).det ≠ 0 := by
    intro m
    have := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    exact exists_cyclic_field _ (by rw [Matrix.charpoly_map]; exact hs.map)
  choose w hw using hloc
  have hsurj : ∀ i : Fin r, ∃ a : R, ∀ m : MaximalSpectrum R,
      Ideal.Quotient.mk m.asIdeal a = w m i := by
    intro i
    obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective (I := fun m : MaximalSpectrum R => m.asIdeal)
      (fun m m' h => MaximalSpectrum.isCoprime_of_ne h) (fun m => w m i)
    exact ⟨a, ha⟩
  choose v hv using hsurj
  refine ⟨v, ?_⟩
  by_contra hn
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits hn
  apply hw ⟨m, hm⟩
  have : w ⟨m, hm⟩ = Ideal.Quotient.mk m ∘ v := funext fun i => (hv i ⟨m, hm⟩).symm
  rw [this, ← krylov_map]
  rw [← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_det] at hmem
  exact hmem

theorem conj_of_charpoly_eq_of_separable : ∀ (R : Type) [CommRing R], Set.Finite {I : Ideal R | I.IsMaximal} →
    ∀ (n : ℕ) (γ δ : Matrix (Fin n) (Fin n) R), γ.charpoly = δ.charpoly → γ.charpoly.Separable →
      ∃ u : GL (Fin n) R, (u : Matrix (Fin n) (Fin n) R) * δ = γ * u := by
  intro R _ hfin n γ δ hχ hs
  obtain ⟨v, hv⟩ := exists_cyclic_of_finite_maximal hfin γ hs
  obtain ⟨w, hw⟩ := exists_cyclic_of_finite_maximal hfin δ (hχ ▸ hs)
  obtain ⟨a, ha⟩ := (isUnit_iff_isUnit_det _).2 hv
  obtain ⟨b, hb⟩ := (isUnit_iff_isUnit_det _).2 hw
  have h1 := GlobalTheory.Orb.mul_krylov_eq γ v
  have h2 := GlobalTheory.Orb.mul_krylov_eq δ w
  rw [← ha] at h1
  rw [← hb, ← hχ] at h2
  refine ⟨a * b⁻¹, ?_⟩
  set C := GlobalTheory.Orb.companionMat n γ.charpoly
  rw [Units.val_mul]
  calc (a : Matrix (Fin n) (Fin n) R) * ↑b⁻¹ * δ = ↑a * ↑b⁻¹ * (δ * ↑b) * ↑b⁻¹ := by
        simp [mul_assoc]
    _ = ↑a * ↑b⁻¹ * (↑b * C) * ↑b⁻¹ := by rw [h2]
    _ = ↑a * C * ↑b⁻¹ := by
        simp [mul_assoc]
    _ = γ * ↑a * ↑b⁻¹ := by rw [h1]
    _ = γ * (↑a * ↑b⁻¹) := by rw [mul_assoc]

end GlobalTheory.SemilocalConj
