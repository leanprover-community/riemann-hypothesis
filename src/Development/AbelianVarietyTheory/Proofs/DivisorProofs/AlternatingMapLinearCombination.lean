module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

namespace GlobalTheory.AlternatingLinearCombination

theorem alternating_map_linear_combination {L M N : Type} [Field L] [AddCommGroup M] [Module L M]
    [AddCommGroup N] [Module L N] {n : ℕ} (f : M [⋀^Fin n]→ₗ[L] N) (g : Fin n → M)
    (a : Fin n → Fin n → L) :
    (f fun i => ∑ l : Fin n, a i l • g l) = Matrix.det (Matrix.of a) • f g := by
  classical
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff L]
  intro φ
  let ψ : (Fin n → L) →ₗ[L] M := Fintype.linearCombination L g
  let F : (Fin n → L) [⋀^Fin n]→ₗ[L] L := (φ.compAlternatingMap f).compLinearMap ψ
  have h := F.eq_smul_basis_det (Pi.basisFun L (Fin n))
  have h1 : F a = φ (f fun i => ∑ l : Fin n, a i l • g l) := by
    simp [F, ψ, Fintype.linearCombination_apply]
  have h2 : F (Pi.basisFun L (Fin n)) = φ (f g) := by
    have : (fun i => ψ (Pi.basisFun L (Fin n) i)) = g := by
      funext i
      simp [ψ]
    change φ (f fun i => ψ (Pi.basisFun L (Fin n) i)) = _
    rw [this]
  have h3 : F a = φ (f g) * Matrix.det (Matrix.of a) := by
    rw [h, AlternatingMap.smul_apply, h2, Pi.basisFun_det_apply, smul_eq_mul]
  rw [map_sub, map_smul, ← h1, h3, smul_eq_mul, mul_comm, sub_self]

end GlobalTheory.AlternatingLinearCombination
