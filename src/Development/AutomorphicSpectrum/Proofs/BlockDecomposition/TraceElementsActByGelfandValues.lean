module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceElementCapelliRecursionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceElementGelfandPolynomialFormulaStatement
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.CapelliGelfand

theorem etr_eq_gelfVal_of_capelli :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ V)
      (χ : Fin (m + 1) → ℂ) (v : V), Formalism.REAL.GlRel E →
      (∀ Y : ℂ, Formalism.REAL.qdet E (Y + (((m + 1 : ℕ) : ℂ) - 1) / 2) v = Formalism.QuantumDeterminants.capP χ Y • v) →
      ∀ k : ℕ, Formalism.REAL.etr E k v = GlobalTheory.Dec.gelfVal χ k • v := by
  intro V _ _ m E χ v hE hq
  have hcap : ∀ Y : ℂ, Formalism.QuantumDeterminants.capP χ Y = ∏ s, (Y + χ s) := by
    intro Y
    rfl
  have hP : ∀ u : ℂ, Formalism.REAL.qdet E u v =
      (∏ s, (Polynomial.X + Polynomial.C (χ s - (m : ℂ) / 2))).eval u • v := by
    intro u
    have h := hq (u - (m : ℂ) / 2)
    have h1 : u - (m : ℂ) / 2 + (((m + 1 : ℕ) : ℂ) - 1) / 2 = u := by
      push_cast
      ring
    rw [h1, hcap] at h
    rw [h, Polynomial.eval_prod]
    congr 1
    refine Finset.prod_congr rfl fun s _ => ?_
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    ring
  intro k
  induction k using Nat.strong_induction_on with
  | _ N ih =>
    rw [GlobalTheory.T.trace_element_capelli_recursion V m E hE _ v hP N (fun k => GlobalTheory.Dec.gelfVal χ k) (fun k hk => ih k hk)]
    rw [GlobalTheory.T.trace_element_gelfand_polynomial_formula m χ N]

end GlobalTheory.CompanionTheory.CapelliGelfand
