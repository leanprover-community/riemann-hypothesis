module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTwistedOrbitalIntegralsEqFinsumParametrised
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

@[expose] public section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

theorem _root_.GlobalTheory.T.sum_twistedOrbitalIntegrals_eq_finsum_parametrised : ∀ (G : Type) [Group G] [TopologicalSpace G] (θ : G →* G) (Kg : Subgroup G) (S : Set G) (f : G → ℂ) (C : Type) (ι : C → G) (N : C → ℂ), (∀ c, ι c ∈ S) → (∀ y ∈ S, ∃ c g, y = g⁻¹ * ι c * θ g) → (∀ c c', (∃ g, ι c' = g⁻¹ * ι c * θ g) → c = c') → (∀ y g, g⁻¹ * y * θ g ∈ S ↔ y ∈ S) → (∀ y g, twOrb θ Kg (g⁻¹ * y * θ g) f = twOrb θ Kg y f) → (∀ c, twOrb θ Kg (ι c) f = N c) → clSum θ Kg S (fun _ => 1) f = ∑ᶠ c, N c := by
  first | exact @GlobalTheory.BCT.ClSumParam.clSum_eq_finsum_param | exact GlobalTheory.BCT.ClSumParam.clSum_eq_finsum_param | (intros; apply GlobalTheory.BCT.ClSumParam.clSum_eq_finsum_param <;> assumption)
