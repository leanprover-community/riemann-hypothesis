module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaurentSeriesPadicExistsPthPowerCombination
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResidueLinearDisjointnessCoeffLtOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Integral

@[expose] public section

open scoped MatrixGroups NNReal
open Polynomial GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois


theorem _root_.GlobalTheory.T.residue_linear_disjointness_coeff_lt_one :
    ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
      IsClo p Ω → ∀ (v : Valuation Ω ℝ≥0), (∀ x : Ω, v x ≤ 1 ↔ IsInt (p := p) x) →
      v (p : Ω) < 1 → ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω),
      IsReb T n ψ → ∀ (d : ℕ) (e : Fin d → Ω) (a : Fin d → Lau p),
      (∀ t, IsInt (p := p) (e t) ∧ IsAlgZp (p := p) (e t)) →
      v (∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t))) < 1 →
      ∀ r : ℤ, v (∑ t, e t * zp Ω ((a t).coeff r)) < 1 := by
  apply _root_.GlobalTheory.K5.ResDisj.coeff_lt_one <;> assumption
