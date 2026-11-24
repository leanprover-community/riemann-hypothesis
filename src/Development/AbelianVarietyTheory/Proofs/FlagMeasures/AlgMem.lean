module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPowSmulMemOfIsLat
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc

namespace GlobalTheory.PowMulMem

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem alg_mem (L : LocE F E) (a : 𝒪[F]) : algebraMap F E (a : F) ∈ L.O := by
  rw [L.O_def]
  exact isIntegral_algebraMap (R := 𝒪[F]) (A := E) (x := a)

theorem exists_pow_mul_mem [IsNonarchimedeanLocalField F] (L : LocE F E) {ϖ : 𝒪[F]}
    (hϖ : Irreducible ϖ) (e : E) : ∃ k : ℕ, algebraMap F E ((ϖ : F) ^ k) * e ∈ L.O := by
  apply GlobalTheory.PowSmulMemLattice.exists_pow_mul_mem_O <;> assumption

theorem exists_pow_smul_mem [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E)
    {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {n : ℕ} {Λ : Submodule L.O (Fin n → E)}
    (hΛ : GlobalTheory.HL.IsLat L Λ) (v : Fin n → E) :
    ∃ k : ℕ, algebraMap F E ((ϖ : F) ^ k) • v ∈ Λ := by
  have hO : ∀ (x : E), x ∈ L.O → ∀ w ∈ Λ, x • w ∈ Λ := fun x hx w hw =>
    Λ.smul_mem (⟨x, hx⟩ : L.O) hw
  have hp : ∀ k : ℕ, algebraMap F E ((ϖ : F) ^ k) ∈ L.O := fun k => by
    rw [map_pow]; exact L.O.pow_mem (alg_mem L ϖ) k
  have hv : v ∈ Submodule.span E (Λ : Set (Fin n → E)) := by rw [hΛ.2]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, hO _ (hp 0) _ hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · have := hO _ (hp b) _ ha
      rwa [smul_smul, ← map_mul, ← pow_add, add_comm b a] at this
    · have := hO _ (hp a) _ hb
      rwa [smul_smul, ← map_mul, ← pow_add] at this
  | smul e x _ hx =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := exists_pow_mul_mem L hϖ e
    refine ⟨a + b, ?_⟩
    have := hO _ hb _ ha
    have h : algebraMap F E ((ϖ : F) ^ (a + b)) • e • x
        = (algebraMap F E ((ϖ : F) ^ b) * e) • algebraMap F E ((ϖ : F) ^ a) • x := by
      rw [smul_smul, smul_smul, pow_add, map_mul]
      congr 1
      ring
    rw [h]
    exact this

end GlobalTheory.PowMulMem
