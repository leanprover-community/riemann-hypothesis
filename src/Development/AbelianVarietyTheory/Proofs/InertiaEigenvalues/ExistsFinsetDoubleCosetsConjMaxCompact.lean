module

public import Formalism.AlgebraicWeights.IsAlgWeight
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryCongruenceConjContainsCongruence
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.ClassFinConj

theorem exists_finset_double_cosets_conj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (h : GAf L n),
    ∃ T : Finset (GAf L n), ∀ g : GAf L n, ∃ γ ∈ GQ L n, ∃ t ∈ T,
      ∃ κ ∈ (Umax L n ⊓ (Umax L n).map (MulAut.conj h).toMonoidHom), g = γ * t * κ := by
  intro L _ _ _ n h
  classical
  obtain ⟨T, hT⟩ := GlobalTheory.DefiniteClassFinite.exists_finset_double_cosets_Umax L n
  obtain ⟨N', hN', hc⟩ := GlobalTheory.CongConjugate.congConj L n h 1 one_pos
  obtain ⟨J, hJ⟩ := GlobalTheory.AlgFormsFin.exists_cover L n hN'
  refine ⟨(T ×ˢ J).image (fun p => p.1 * p.2), fun g => ?_⟩
  obtain ⟨γ, t, u, ht, hu, e⟩ := hT g
  obtain ⟨j, hj, κ, hκ, eu⟩ := hJ u hu
  refine ⟨(γ : GAf L n), γ.2, t * j, Finset.mem_image.2 ⟨(t, j), Finset.mem_product.2 ⟨ht, hj⟩, rfl⟩, κ,
    Subgroup.mem_inf.2 ⟨hκ.1, Subgroup.mem_map.2 ⟨h⁻¹ * κ * h, (hc κ hκ).1, ?_⟩⟩, ?_⟩
  · simp [MulAut.conj_apply, mul_assoc]
  · rw [e, eu]; simp only [mul_assoc]

end GlobalTheory.ClassFinConj
