module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LcountNorm
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.fzkLaw : UpperTheory.V.Z.Sym.Loc.FzkLaw := by
  intro O K _ _ _ _ _ Δ hL χ hχ
  have inj : Function.Injective (algebraMap O K) := by
    haveI := hL.frac
    exact IsFractionRing.injective O K
  have ent : ∀ b : Kˣ, ((Matrix.GeneralLinearGroup.scalar (Fin 2) b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 = b := by
    intro b
    simp
  have key : ∀ a : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ KG O K → χ a = 1 := by
    rintro a ⟨M, hM⟩
    have a1 : algebraMap O K ((M : Matrix (Fin 2) (Fin 2) O) 0 0) = (a : K) := by
      have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) hM
      exact this.trans (ent a)
    have hM' : Matrix.GeneralLinearGroup.map (algebraMap O K) M⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹ := by
      rw [map_inv, hM, map_inv]
    have a2 : algebraMap O K (((M⁻¹ : GL (Fin 2) O) : Matrix (Fin 2) (Fin 2) O) 0 0) = ((a⁻¹ : Kˣ) : K) := by
      have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) hM'
      exact this.trans (ent a⁻¹)
    have hp : (M : Matrix (Fin 2) (Fin 2) O) 0 0 * ((M⁻¹ : GL (Fin 2) O) : Matrix (Fin 2) (Fin 2) O) 0 0 = 1 := by
      apply inj
      rw [map_mul, a1, a2, Units.mul_inv, map_one]
    have hu : Units.map (algebraMap O K : O →* K) (Units.mkOfMulEqOne _ _ hp) = a := by
      ext
      simpa using a1
    rw [← hu]
    exact hχ _
  refine ⟨fun g hg => ?_, fun z k hk => ?_⟩
  · unfold fZK
    rw [dite_eq_right]
    rintro ⟨z, hz⟩
    apply hg
    rw [← mul_inv_cancel_left (Matrix.GeneralLinearGroup.scalar (Fin 2) z) g]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨z, rfl⟩) (Subgroup.mem_sup_right hz)
  · have hex : ∃ w, (Matrix.GeneralLinearGroup.scalar (Fin 2) w)⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 2) z * k) ∈ KG O K :=
      ⟨z, by rw [inv_mul_cancel_left]; exact hk⟩
    unfold fZK
    rw [dite_eq_left hex]
    have hw := hex.choose_spec
    have hs : Matrix.GeneralLinearGroup.scalar (Fin 2) (hex.choose⁻¹ * z) ∈ KG O K := by
      have e : Matrix.GeneralLinearGroup.scalar (Fin 2) (hex.choose⁻¹ * z) = (Matrix.GeneralLinearGroup.scalar (Fin 2) hex.choose)⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 2) z * k) * k⁻¹ := by
        rw [map_mul, map_inv]
        simp [mul_assoc]
      rw [e]
      exact Subgroup.mul_mem _ hw (Subgroup.inv_mem _ hk)
    have h1 := key _ hs
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    rw [h1]
