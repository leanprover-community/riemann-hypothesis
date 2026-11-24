module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral

@[expose] public section

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

theorem UpperTheory.V.Th.Coc.liftConj :
    ∀ {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ} {E : Type} [Ring E] [Algebra R E] (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ ρ' : E →+* Matrix (Fin n) (Fin n) O) (τ : E → R) (c : O) (Q : GL (Fin n) O) (d : E →+ Matrix (Fin n) (Fin n) X), (∀ a, ρ a = (Q : Matrix (Fin n) (Fin n) O) * ρ' a * ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O)) → IsLift x δ ρ' τ c d → ∃ d' : E →+ Matrix (Fin n) (Fin n) X, IsLift x δ ρ τ c d' ∧ ∀ a, d' a = bar X (Q : Matrix (Fin n) (Fin n) O) * d a * bar X ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) := by
  intro O R X _ _ _ _ _ n E _ _ x δ ρ ρ' τ c Q d hρ hL
  have hbm : ∀ A B : Matrix (Fin n) (Fin n) O, bar X (A * B) = bar X A * bar X B := by
    intro A B
    simp [bar, Matrix.map_mul]
  have hbar1 : bar X (1 : Matrix (Fin n) (Fin n) O) = 1 := by
    simp [bar]
  have hl : bar X ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * bar X (Q : Matrix (Fin n) (Fin n) O) = 1 := by
    rw [← hbm, Units.inv_mul, hbar1]
  have hbρ : ∀ a, bar X (ρ a) = bar X (Q : Matrix (Fin n) (Fin n) O) * bar X (ρ' a) * bar X ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) := by
    intro a
    rw [hρ, hbm, hbm]
  set P := bar X (Q : Matrix (Fin n) (Fin n) O) with hPdef
  set Pi := bar X ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) with hPidef
  refine ⟨AddMonoidHom.mk' (fun a => P * d a * Pi) (fun a b => by rw [map_add (f := _), mul_add, add_mul]), ?_, fun a => rfl⟩
  constructor
  · intro a b
    simp only [AddMonoidHom.mk'_apply]
    rw [hL.mul, hbρ, hbρ]
    have e1 : P * d a * Pi * (P * bar X (ρ' b) * Pi) = P * (d a * bar X (ρ' b)) * Pi := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Pi P, hl, Matrix.one_mul]
    have e2 : P * bar X (ρ' a) * Pi * (P * d b * Pi) = P * (bar X (ρ' a) * d b) * Pi := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Pi P, hl, Matrix.one_mul]
    rw [e1, e2, mul_add, add_mul]
  · intro r a
    simp only [AddMonoidHom.mk'_apply]
    rw [hL.smul, hbρ, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]
  · intro a
    simp only [AddMonoidHom.mk'_apply]
    rw [Matrix.trace_mul_cycle, hl, Matrix.one_mul, hL.tr]
