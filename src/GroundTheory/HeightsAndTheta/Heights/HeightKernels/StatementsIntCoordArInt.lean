module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsIntCoordChange
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

def IntCoordArInt.Statement : Prop :=
  ∀ (T T₂ : Type) [Fintype T] [DecidableEq T] [Fintype T₂] [DecidableEq T₂] (A : Matrix T T₂ ℤ)
    (B : Matrix T₂ T ℤ) (_ : A * B = 1) (hBA : B * A = 1) (Q : Ideal (MRing (dualBlocks T))) (e : ℕ)
    (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T))
    (Ab : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T)) (s : MRing (dualBlocks T)),
    IsArithVar Q (e + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm Ab → IsSectionOn Q Ab s →
    arInt (Q.comap (intCoordSubst A)) (intCoordSubst B s) (intCoordLine B ⟨A, hBA⟩ Ab)
        (fun j => intCoordLine B ⟨A, hBA⟩ (L j)) =
      arInt Q s Ab L

def intCoordSwap : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

theorem intCoordSwap_mul_self : intCoordSwap * intCoordSwap = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [intCoordSwap, Matrix.mul_apply, Fin.sum_univ_two]

end

end GroundTheory.Heights₂.Heights
