module

public import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.Analytic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AutomorphicArithmetic.PrimeDiscriminants.Scales
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MeanSquareHypWIff
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private theorem gauss_sum_function_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) :
    Formalism.HC.An.gChi χ y = G0 χ y := by
  have hmax : ∀ n ∈ Icc 1 ⌊y⌋₊, max (y / n - 1) 0 = y / n - 1 := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
    have hy : 0 ≤ y := by
      by_contra hc
      rw [Nat.floor_of_nonpos (le_of_lt (not_le.1 hc))] at h2
      omega
    have hny : (n : ℝ) ≤ y := (Nat.le_floor_iff hy).1 h2
    have : 1 ≤ y / n := (one_le_div hn0).2 hny
    exact max_eq_left (by linarith)
  unfold Formalism.HC.An.gChi G0
  by_cases h : χ = 1
  · rw [if_pos h, if_pos h]
    unfold Formalism.HC.An.G G1
    rw [Finset.sum_congr rfl fun n hn => by rw [hmax n hn]]
  · rw [if_neg h, if_neg h]
    unfold Formalism.HC.An.sumLamChi Gchi Formalism.HC.An.logDerivativeAtOne logDerivLAtOne
    rw [Finset.sum_congr rfl fun n hn => by rw [hmax n hn]]

private theorem isReal_of_sq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (h2 : χ ^ 2 = 1) (a : ZMod N) :
    (χ a).im = 0 := by
  rcases MulChar.isQuadratic_iff_sq_eq_one.2 h2 a with h | h | h <;> simp [h]

end QH

end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

end GlobalTheory.EX
