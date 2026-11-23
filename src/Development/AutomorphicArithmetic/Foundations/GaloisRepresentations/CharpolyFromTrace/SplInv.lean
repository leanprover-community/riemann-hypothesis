module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.KillTransferAlt
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
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.LimitEig
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.LinearAlgebra.Charpoly.Basic
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
open GlobalTheory.WeilDeligne GlobalTheory.Cong UpperTheory.Gal.NearKilling

private theorem trace_eq_of_charpoly {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] {f : Module.End ℂ V} {g : Module.End ℂ V'}
    (e : f.charpoly = g.charpoly) : LinearMap.trace ℂ V f = LinearMap.trace ℂ V' g := by
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _),
    Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _), e]

private theorem kill_mul (kt : KillTransfer) {I V V' : Type} [Group I] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
    (ρ : Representation ℂ I V) (ρ' : Representation ℂ I V') (hf : (Set.range ρ).Finite)
    (ht : ∀ s, LinearMap.trace ℂ V (ρ s) = LinearMap.trace ℂ V' (ρ' s)) (s γ : I) (a : ℂ) (q : ℂ[X]) :
    ((ρ' s - a • 1) * aeval (ρ' γ) q = 0 → (ρ s - a • 1) * aeval (ρ γ) q = 0) ∧
    (aeval (ρ' γ) q * (ρ' s - a • 1) = 0 → aeval (ρ γ) q * (ρ s - a • 1) = 0) := by
  have key : ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (r : Representation ℂ I W),
      r.asAlgebraHom (MonoidAlgebra.single s 1 - a • 1) = r s - a • 1 ∧
      r.asAlgebraHom (aeval (MonoidAlgebra.single γ (1 : ℂ)) q) = aeval (r γ) q := by
    intro W _ _ r
    refine ⟨?_, ?_⟩
    · rw [map_sub, map_smul, map_one, Representation.asAlgebraHom_single_one]
    · rw [← Polynomial.aeval_algHom_apply, Representation.asAlgebraHom_single_one]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := kt I V V' ρ ρ' hf ht ((MonoidAlgebra.single s 1 - a • 1) * aeval (MonoidAlgebra.single γ (1 : ℂ)) q)
      (by rw [map_mul, (key ρ').1, (key ρ').2]; exact h)
    rwa [map_mul, (key ρ).1, (key ρ).2] at this
  · have := kt I V V' ρ ρ' hf ht (aeval (MonoidAlgebra.single γ (1 : ℂ)) q * (MonoidAlgebra.single s 1 - a • 1))
      (by rw [map_mul, (key ρ').1, (key ρ').2]; exact h)
    rwa [map_mul, (key ρ).1, (key ρ).2] at this
