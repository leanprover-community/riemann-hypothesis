module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

theorem GlobalTheory.PMon.galois_inv_period_matrix : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (ρ : ↥(GK K) →* GL n ℚ_[l]) (M : GL n ℂ_[l]), (∀ g : ↥(GK K), (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) * (M : Matrix n n ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = M) → ∀ g : ↥(GK K), ((M⁻¹ : GL n ℂ_[l]) : Matrix n n ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = ((M⁻¹ : GL n ℂ_[l]) : Matrix n n ℂ_[l]) * (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) := by
  intro l _ n _ _ K ρ M h g
  set σ := Formalism.Per.σC (g : GQ l) with hσ
  have h1 : (M : Matrix n n ℂ_[l]).map σ * ((M⁻¹ : GL n ℂ_[l]) : Matrix n n ℂ_[l]).map σ = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero σ) (map_one σ)]
  have h2 := h g
  set R := (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l])
  have h3 : R = (M : Matrix n n ℂ_[l]) * ((M⁻¹ : GL n ℂ_[l]) : Matrix n n ℂ_[l]).map σ := by
    calc R = R * ((M : Matrix n n ℂ_[l]).map σ * ((M⁻¹ : GL n ℂ_[l]) : Matrix n n ℂ_[l]).map σ) := by rw [h1, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h2]
  rw [h3, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
