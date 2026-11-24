module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.TwoBlockModule
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.HSClosing
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def TwoBlockModuleFinite.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (c : κ) (l : Ix κ → ℤ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j →
    IsMultiHomogIdeal (twoBlockMOuter x (matAct B x) c) ∧ IsMultiHomogIdeal (twoBlockMInner x (matAct B x) l) ∧
      twoBlockMInner x (matAct B x) l ≤ twoBlockMOuter x (matAct B x) c ∧
      (∃ N : ℕ, 0 < N ∧ ∀ f ∈ twoBlockMOuter x (matAct B x) c,
        (N : MRing (FinTwoTypeFamily κ)) * f ∈ twoBlockMInner x (matAct B x) l) ∧
      ∀ W : Ideal (MRing (FinTwoTypeFamily κ)), W.IsPrime → twoBlockMInner x (matAct B x) l ≤ W → IsRelevant W →
        ringKrullDim (MRing (FinTwoTypeFamily κ) ⧸ W) ≤ ((D + Fintype.card (Fin 2) : ℕ) : WithBot ℕ∞)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
