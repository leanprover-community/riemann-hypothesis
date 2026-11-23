module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwistBaseCoefficientRingResidueFieldFinite
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.Member.DeltaTame

theorem delta_tame_and_15 : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (P : PlE D.host), P ∈ T.pD i →
    ((15 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P → ∀ σ ∈ Ine (F := D.host.E) A,
      ∃ N : ℕ, T.delta i σ ^ (15 ^ N) = 1 := by
  intro D T i P hP
  refine ⟨?_, ?_⟩
  · intro h15
    have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := Ideal.absNorm_mem _
    have hmod := T.delta_tame i P hP
    have hdecomp : Ideal.absNorm P.asIdeal = 15 * (Ideal.absNorm P.asIdeal / 15) + 1 := by
      have := Nat.div_add_mod (Ideal.absNorm P.asIdeal) 15
      omega
    rw [hdecomp] at hmem
    push_cast at hmem h15
    have h1 : (1 : 𝓞 D.host.E) ∈ P.asIdeal := by
      have hm2 : (15 : 𝓞 D.host.E) * ((Ideal.absNorm P.asIdeal / 15 : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal :=
        P.asIdeal.mul_mem_right _ h15
      have := P.asIdeal.sub_mem hmem hm2
      simpa using this
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  · intro A hA σ hσ
    have h15 := T.delta_15 i P hP A hA
    have hfin : Finite ((Ine (F := D.host.E) A).map (T.delta i)) :=
      Nat.finite_of_card_ne_zero (by rw [h15]; norm_num)
    have hpow := pow_card_eq_one' (G := (Ine (F := D.host.E) A).map (T.delta i))
      (x := ⟨T.delta i σ, Subgroup.mem_map_of_mem _ hσ⟩)
    rw [h15] at hpow
    refine ⟨1, ?_⟩
    have := congrArg Subtype.val hpow
    simpa using this

end GlobalTheory.Member.DeltaTame
