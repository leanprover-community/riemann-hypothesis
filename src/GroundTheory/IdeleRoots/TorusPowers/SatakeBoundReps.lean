module

public import GroundTheory.AutomorphicForms.SphericalMinuscule
public import GroundTheory.AutomorphicForms.AffineBruhat
public import GroundTheory.AutomorphicForms.MacdonaldHecke
public import GroundTheory.IdeleRoots.TorusPowers.SatakeBoundGroup
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

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.BlockD

namespace SatakeBound

section Group

variable {G : Type} [Group G] {K : Subgroup G} {α : G} {R : Finset G}

end Group

open GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GLnLocal Iwasawa Finset Matrix
open scoped ValuativeRel

attribute [local instance] GroundTheory.Automorphic.Spherical.fintypeResidue

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem one_apply_mem_integer (i j : Fin n) : (1 : Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F] := by
  rw [Matrix.one_apply]
  split_ifs
  · exact (𝒪[F]).one_mem
  · exact (𝒪[F]).zero_mem

theorem unipC_mem_integralGL (S : Finset (Fin n)) (c : Pairs S → 𝓀[F]) : unipC S c ∈ integralGL F n := by
  rw [mem_integralGL_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · change (1 + cMat S c) i j ∈ 𝒪[F]
    rw [Matrix.add_apply]
    exact (𝒪[F]).add_mem (one_apply_mem_integer i j) (cMat_mem c i j)
  · change (1 - cMat S c) i j ∈ 𝒪[F]
    rw [Matrix.sub_apply]
    exact (𝒪[F]).sub_mem (one_apply_mem_integer i j) (cMat_mem c i j)

theorem exists_torusPow_lamS_eq {A B : Finset (Fin n)} (h : A.card = B.card) :
    ∃ P ∈ integralGL F n, torusPow F n (lamS A) = P⁻¹ * torusPow F n (lamS B) * P := by
  obtain ⟨σ, hσ⟩ := exists_perm_mem_iff h
  refine ⟨permGL F σ, GLnLocal.permGL_mem_integralGL F n σ, ?_⟩
  rw [permGL_conj_torusPow, lamS_comp_of_mem_iff hσ]

end SatakeBound

end GroundTheory.BlockD
