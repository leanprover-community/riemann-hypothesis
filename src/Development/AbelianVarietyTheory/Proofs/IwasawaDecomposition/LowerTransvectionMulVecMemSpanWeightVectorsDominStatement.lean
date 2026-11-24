module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerTransvectionMulVecMemSpanWeightVectorsDomin
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

theorem _root_.GlobalTheory.T.lowerTransvection_mulVec_mem_spanWeightVectorsDominatedBy : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (lam ν : Fin n → ℤ), DomLE ν lam → ∀ (w : ι → ℂ), IsWtVec Φ ν w → ∀ (i j : Fin n), j < i → ∀ (s : ℂ) (T : GL (Fin n) ℂ), T.val = transvection i j s → Φ T *ᵥ w ∈ Sle Φ lam := by
  first | exact @GlobalTheory.AlgWtHW.lowerTransvection_mulVec_mem_Sle | exact GlobalTheory.AlgWtHW.lowerTransvection_mulVec_mem_Sle | (intros; apply GlobalTheory.AlgWtHW.lowerTransvection_mulVec_mem_Sle <;> assumption)
