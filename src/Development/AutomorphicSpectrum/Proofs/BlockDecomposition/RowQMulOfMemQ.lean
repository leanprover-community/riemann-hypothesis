module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMatMir
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun Matrix

namespace GlobalTheory.CompanionTheory.BZPhiPhi

theorem rowQ_mul_of_mem_Q (k : Type) [Field k] (n : ℕ) (q g : Mir k (n + 1)) (hq : q ∈ Q k n) :
    rowQ k n (q * g) = rowQ k n g := by
  have hb : (blockMat k (n + 1) ((q : GL (Fin (n + 2)) k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k)) (Fin.last n) =
      eLast k n := by
    have h := (mem_Mir_iff k (mirabolicProjection k (n + 1) q)).1 hq
    exact h
  have hg : ∀ j : Fin (n + 1), ((g : GL (Fin (n + 2)) k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k)
      (Fin.last (n + 1)) (Fin.castSucc j) = 0 := by
    intro j
    have := congrFun ((mem_Mir_iff k (g : GL (Fin (n + 2)) k)).1 g.2) (Fin.castSucc j)
    simpa [eLast, Fin.castSucc_ne_last] using this
  funext j
  have hb' : ∀ l : Fin (n + 1), ((q : GL (Fin (n + 2)) k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k)
      (Fin.castSucc (Fin.last n)) (Fin.castSucc l) = eLast k n l := fun l => congrFun hb l
  simp only [rowQ, Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_castSucc (n := n + 1), hg, hb', mul_zero, add_zero]
  simp [eLast, Pi.single_apply]

end GlobalTheory.CompanionTheory.BZPhiPhi

end
