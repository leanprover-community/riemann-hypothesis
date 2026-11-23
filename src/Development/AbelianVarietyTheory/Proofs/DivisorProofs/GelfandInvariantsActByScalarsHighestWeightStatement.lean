module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GelfandInvariantsActByScalarsHighestWeight
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.gelfand_invariants_act_by_scalars_highest_weight : ∀ (n : ℕ) (Hm : Mt n) (q : ℕ) (x₀ : Mt n) (w : Fin n → ℤ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mt n → (H →L[ℂ] H)), OrthFr Hm q x₀ → IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ → IsIrredOn (Formalism.QuantumDeterminants.UH Hm) σ → ∀ v₀, v₀ ≠ 0 → SmoothVec (lieH Hm) σ v₀ → (∀ a c : Fin n, a ≤ c → dRepC Hm σ (x₀ * Matrix.single a c 1 * x₀⁻¹) v₀ = if a = c then (w a : ℂ) • v₀ else 0) → ∀ k, ∃ c : ℂ, ∀ v, SmoothVec (lieH Hm) σ v → gelfRep Hm σ k v = c • v := by
  first | exact @GlobalTheory.HolDict.GelfScalar.gelfRep_scalar | exact GlobalTheory.HolDict.GelfScalar.gelfRep_scalar | (intros; apply GlobalTheory.HolDict.GelfScalar.gelfRep_scalar <;> assumption)
