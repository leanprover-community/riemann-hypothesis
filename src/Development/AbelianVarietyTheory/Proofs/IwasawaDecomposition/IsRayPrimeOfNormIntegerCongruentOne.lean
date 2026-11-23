module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
import Formalism.LocalToGlobal.Divisibility.ConjugationAtDistinguishedPlace
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.RayPrimeOfNorm

theorem isRayPrime_of_norm_eq : ∀ (D : D7) (i : Fin 2) (jE : D.host.E →+* Qb), (D.host.g i).Prime → (∃ π : 𝓞 D.host.E, (π : D.host.E) ∈ D.host.K ∧ (π : D.host.E) * D.host.conj (π : D.host.E) = (D.host.g i : D.host.E) ∧ (π - 1) ∈ Ideal.span {((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E)}) → IsRayPrime (GlobalTheory.HeightCounting.KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g i) := by
  intro D i jE hp ⟨π, hK, hnorm, hm⟩
  letI : Algebra D.host.E Qb := jE.toAlgebra
  haveI : IsScalarTower ℚ D.host.E Qb := IsScalarTower.of_algebraMap_eq fun x =>
    RingHom.congr_fun (Subsingleton.elim (algebraMap ℚ Qb) (jE.comp (algebraMap ℚ D.host.E))) x
  let σ : Qb →ₐ[ℚ] Qb := (D.host.conj : D.host.E →ₐ[ℚ] D.host.E).liftNormal Qb
  have hσ : ∀ x : D.host.E, σ (jE x) = jE (D.host.conj x) := fun x =>
    AlgHom.liftNormal_commutes (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) Qb x
  refine ⟨hp, jE (π : D.host.E), (IntermediateField.mem_map _).2 ⟨_, hK, rfl⟩, ?_, ?_, σ, ?_⟩
  · exact (RingOfIntegers.isIntegral_coe π).map jE.toIntAlgHom
  · obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hm
    by_cases hm0 : (((D.host.QS * D.host.q * D.host.d : ℕ)) : Qb) = 0
    · rw [hm0, div_zero]; exact isIntegral_zero
    · have e : (jE (π : D.host.E) - 1) / (((D.host.QS * D.host.q * D.host.d : ℕ)) : Qb) = jE (y : D.host.E) := by
        rw [div_eq_iff hm0]
        have e1 := congrArg (fun z : 𝓞 D.host.E => jE (algebraMap (𝓞 D.host.E) D.host.E z)) hy
        simp only [map_mul, map_sub, map_one, map_natCast] at e1
        push_cast at e1 ⊢
        exact e1.symm
      rw [e]
      exact (RingOfIntegers.isIntegral_coe y).map jE.toIntAlgHom
  · rw [hσ, ← map_mul, hnorm, map_natCast]

end GlobalTheory.RayPrimeOfNorm
