module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SameGenusFix
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulOfMemSmulLocF
public import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovol
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsLocUnif

@[expose] public section

open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem isLattice_span {ι' : Type} [Finite ι'] (β : ι' → V)
    (hβ : Submodule.span K (Set.range β) = ⊤) :
    Submodule.IsFullLattice K (Submodule.span (𝓞 K) (Set.range β)) := by
  let : Submodule.IsLattice K (Submodule.span (𝓞 K) (Set.range β)) :=
    Submodule.IsLattice.of_fg K (Submodule.fg_span (Set.finite_range β))
  exact { span_eq_top := (Submodule.span_span_of_tower (𝓞 K) K (Set.range β)).trans hβ }

def rdualF (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔭 : Ideal (𝓞 F)) (y : V) : Submodule (𝓞 K) V :=
  (locF 𝔭 (1 : Submodule (𝓞 K) K)).comap ((h y).restrictScalars (𝓞 K))

def ldualF (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔭 : Ideal (𝓞 F)) (x : V) : Submodule (𝓞 K) V where
  carrier := {y | h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add (f := _), LinearMap.add_apply] at *
    exact Submodule.add_mem _ ha hb
  smul_mem' := by
    intro c z hz
    simp only [Set.mem_ofPred_eq] at *
    obtain ⟨r, hr⟩ := Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range c
    rw [← algebraMap_smul K c z, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply,
      ← hr, ← smul_eq_mul, algebraMap_smul]
    exact Submodule.smul_mem _ r hz

theorem le_dualF_of_gram (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) {𝔭 : Ideal (𝓞 F)}
    (hp : 𝔭.IsPrime) {ι' : Type} (β : ι' → V)
    (hβ : ∀ i j, h (β i) (β j) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)) :
    locF 𝔭 (Submodule.span (𝓞 K) (Set.range β)) ≤
      dualF h 𝔭 (locF 𝔭 (Submodule.span (𝓞 K) (Set.range β))) := by
  have key : ∀ y ∈ Submodule.span (𝓞 K) (Set.range β), ∀ x ∈ Submodule.span (𝓞 K) (Set.range β),
      h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
    intro y hy x hx
    have hx' : Submodule.span (𝓞 K) (Set.range β) ≤ rdualF h 𝔭 y := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have hy' : Submodule.span (𝓞 K) (Set.range β) ≤ ldualF h 𝔭 (β j) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact hβ i j
      exact hy' hy
    exact hx' hx
  intro x hx
  show ∀ y ∈ _, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
  intro y hy
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff hp _ x).1 hx
  obtain ⟨s, hs, hsy⟩ := (LocF.mem_locF_iff hp _ y).1 hy
  have := key _ hsy _ htx
  rw [localizedQuotients.form_smul hF] at this
  obtain ⟨u, hu, hux⟩ := (LocF.mem_locF_iff hp _ _).1 this
  refine (LocF.mem_locF_iff hp _ _).2 ⟨u * (s * t), fun hm => ?_, ?_⟩
  · rcases hp.mem_or_mem hm with h1 | h1
    · exact hu h1
    · exact (hp.mem_or_mem h1).elim hs ht
  · rw [Algebra.smul_def] at hux ⊢
    rw [map_mul, map_mul] at hux ⊢
    simpa [mul_assoc, mul_comm, mul_left_comm] using hux

end Formalism.L2.SG.Pf.GluingBases
