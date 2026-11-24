module

public import Formalism.RealPlaceAnalysis.StatementE
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AntisymProdEqSumQuantumMinor
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.HermitianCurvature.StatementFr
import Formalism.HermitianCurvature.StatementI
import Formalism.HermitianCurvature.StatementR
import Formalism.HermitianCurvature.StatementWd

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.antisym_prod_eq_sum_quantumMinor : ∀ (A : Type) [Ring A] [Algebra ℂ A] (p m : ℕ) (E : Fin (p + m) → Fin (p + m) → A) (Q : Matrix (Fin m) (Fin (p + m)) ℂ) (Λ : Matrix (Fin (p + m)) (Fin p) ℂ) (N : Matrix (Fin p) (Fin p) ℂ) (w : ℂ), ∑ σ : Equiv.Perm (Fin (p + m)), (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k : Fin p, (Λ * N) (σ (Fin.castAdd m k)) k) • (List.ofFn fun k : Fin m => ∑ d, Q k d • Tm E (w - ((k : ℕ) : ℂ)) (σ (Fin.natAdd p k)) d).prod = N.det • ∑ c : Fin m → Fin (p + m), ∑ d : Fin m → Fin (p + m), ((Matrix.of fun a : Fin (p + m) => Fin.append (Λ a) (fun k : Fin m => if a = c k then (1 : ℂ) else 0)).det * ((∏ k, Q k (d k)) * ((m.factorial : ℕ) : ℂ)⁻¹)) • qminor E c d w := by
  first | exact @GlobalTheory.ScalarColsMinor.antisym_prod_eq_sum_qminor | exact GlobalTheory.ScalarColsMinor.antisym_prod_eq_sum_qminor | (intros; apply GlobalTheory.ScalarColsMinor.antisym_prod_eq_sum_qminor <;> assumption)
