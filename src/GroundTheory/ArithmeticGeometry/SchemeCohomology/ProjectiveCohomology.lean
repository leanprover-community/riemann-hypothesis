module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjCechCompute
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechOrdered
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjTwistLeray
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite MvPolynomial

universe w' u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjSpace

variable {A : Type u} [CommRing A] {n : ℕ}
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology (projectiveSpace A n).toTopCat) AddCommGrpCat.{u})]

theorem nonempty_HTop_equiv (k : ℤ) (hn : 0 < n) :
    Nonempty (Sheaf.H.{w'} (modulesAb (twistingSheaf (grading A n) k)) n ≃+
      (NegMon (n := n) k →₀ A)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hCech := nonempty_cechH_equiv_H_twist (𝒜 := grading A (m + 1))
    (fun j => MvPolynomial.X j) (fun j => X_mem j) iSup_stdOpen k (m + 1)
  obtain ⟨e⟩ := hCech
  exact ⟨e.symm.trans (cechHTopEquiv k m)⟩

theorem subsingleton_H (k : ℤ) {q : ℕ} (hq0 : 0 < q) (hqn : q ≠ n) :
    Subsingleton (Sheaf.H.{w'} (modulesAb (twistingSheaf (grading A n) k)) q) := by
  have hCech := nonempty_cechH_equiv_H_twist (𝒜 := grading A n)
    (fun j => MvPolynomial.X j) (fun j => X_mem j) iSup_stdOpen k q
  obtain ⟨e⟩ := hCech
  have hSubsingleton :
      Subsingleton (cechH (twistAb (A := A) (n := n) k) (cover (A := A) (n := n)) q) := by
    rcases Nat.lt_or_gt_of_ne hqn with h | h
    · exact subsingleton_cechH_of_lt hq0 h
    · have hcard : Fintype.card (Fin (n + 1)) ≤ q := by simpa using h
      exact CechOrdered.subsingleton_cechH hcard hq0
  exact @Equiv.subsingleton _ _ e.symm.toEquiv hSubsingleton

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
