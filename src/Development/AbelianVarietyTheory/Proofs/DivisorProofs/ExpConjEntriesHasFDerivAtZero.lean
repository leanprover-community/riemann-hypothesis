module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Matrix.Normed
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

namespace GlobalTheory

theorem exp_conj_entries_hasFDerivAt_zero : ∀ (n : ℕ) (ι : Type) [Fintype ι] (A : (ι → ℂ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) (p : ι → Fin n × Fin n), (∃ L : (ι → ℂ) →L[ℝ] (ι → ℂ), (∀ w x, L w x = A w (p x).1 (p x).2) ∧ HasFDerivAt (fun (w : ι → ℂ) (x : ι) => (NormedSpace.exp (A w) : Matrix (Fin n) (Fin n) ℂ) (p x).1 (p x).2) L 0) ∧ ∀ s : Matrix (Fin n) (Fin n) ℂ, ∃ L : (ι → ℂ) →L[ℝ] (ι → ℂ), (∀ w x, L w x = (s * A w - A w * s) (p x).1 (p x).2) ∧ HasFDerivAt (fun (w : ι → ℂ) (x : ι) => (NormedSpace.exp (-A w) * s * NormedSpace.exp (A w) : Matrix (Fin n) (Fin n) ℂ) (p x).1 (p x).2) L 0 := by
  intro n ι _ A p
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  let E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (ι → ℂ) :=
    { toFun := fun M x => M (p x).1 (p x).2
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let Ec := LinearMap.toContinuousLinearMap E
  let Ac := LinearMap.toContinuousLinearMap A
  have hA0 : Ac 0 = 0 := map_zero _
  have hnA0 : (-Ac) 0 = 0 := map_zero _
  have h1 : HasFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _)
      (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] _) (Ac 0) := by
    rw [hA0]; exact hasFDerivAt_exp_zero
  have h1' : HasFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _)
      (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] _) ((-Ac) 0) := by
    rw [hnA0]; exact hasFDerivAt_exp_zero
  have hexpA : HasFDerivAt (fun w => NormedSpace.exp (Ac w))
      ((1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] _).comp Ac) 0 :=
    h1.comp (0 : ι → ℂ) Ac.hasFDerivAt
  have hexpN : HasFDerivAt (fun w => NormedSpace.exp ((-Ac) w))
      ((1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] _).comp (-Ac)) 0 :=
    h1'.comp (0 : ι → ℂ) (-Ac).hasFDerivAt
  refine ⟨⟨_, ?_, (Ec.hasFDerivAt).comp (0 : ι → ℂ) hexpA⟩, fun s => ?_⟩
  · intro w x; rfl
  · have hprod := (hexpN.mul' (hasFDerivAt_const s (0 : ι → ℂ))).mul' hexpA
    refine ⟨_, ?_, (Ec.hasFDerivAt).comp (0 : ι → ℂ) hprod⟩
    intro w x
    have hA0' : A 0 = 0 := map_zero A
    simp only [Ec, E, Ac, hA0', NormedSpace.exp_zero, Pi.mul_apply, map_zero, neg_zero]
    change ((1 * s) * A w + (1 * 0 + (-(A w)) * s) * 1 : Matrix (Fin n) (Fin n) ℂ) (p x).1 (p x).2 = (s * A w - A w * s) (p x).1 (p x).2
    rw [one_mul, mul_zero, zero_add, mul_one, neg_mul, ← sub_eq_add_neg]

end GlobalTheory
