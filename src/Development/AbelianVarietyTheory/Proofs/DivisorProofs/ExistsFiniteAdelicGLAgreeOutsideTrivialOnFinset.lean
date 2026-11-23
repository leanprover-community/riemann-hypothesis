module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SatakeComb

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

namespace GlobalTheory

theorem outsideS_elt : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (k : GL (Fin a) (Af E)), ∃ k' : GL (Fin a) (Af E), (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k' = GeneralLinearGroup.map (pLoc E w) k) ∧ ∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k' = 1 := by
  intro E _ _ a S k
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨k, fun w _ => rfl, fun w hw => absurd hw (Finset.notMem_empty w)⟩
  | insert w S hwS ih =>
    obtain ⟨k', h1, h2⟩ := ih
    refine ⟨k' * (locGL E a w (GeneralLinearGroup.map (pLoc E w) k'))⁻¹, ?_, ?_⟩
    · intro v hv
      have hvw : v ≠ w := fun e => hv (e ▸ Finset.mem_insert_self _ _)
      rw [map_mul, map_inv, pLoc_locGL_of_ne hvw, inv_one, mul_one]
      exact h1 v (fun h => hv (Finset.mem_insert_of_mem h))
    · intro v hv
      rw [map_mul, map_inv]
      by_cases hvw : v = w
      · subst hvw; rw [pLoc_locGL, mul_inv_cancel]
      · rw [pLoc_locGL_of_ne hvw, inv_one, mul_one]
        exact h2 v ((Finset.mem_insert.1 hv).resolve_left hvw)

end GlobalTheory
