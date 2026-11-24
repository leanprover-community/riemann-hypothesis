module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockBoundUniformiser
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section Level

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

def phisB (j : Fin G.T.t → ℕ) (jp : ℕ) :
    MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p] :=
  (List.finRange G.T.t).foldr (fun i acc =>
    Formalism.GM.tiePhi (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i), c))
      (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i + 1), c))
      ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i))) ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i + 1)))
      (G.T.z i) ∘ₗ acc) LinearMap.id

def bePhi (j : Fin G.T.t → ℕ) (jp : ℕ) (u v : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) : ℚ_[p] :=
  Formalism.GM.M.fockK (phisB p (r := r) G j jp u) v / (degFact G j jp : ℚ_[p])

end Level

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestPlusA (CM : ℝ) : Prop :=
  ∀ dl ∈ clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl aTop,
    Formalism.GM.M.bad X.p (bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2)
              (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) ⌊D1r C0 CE1 CE2 X CM⌋ ≤
      bY C0 CE1 CE2 X aTop x.1 x.2 ⌊D1r C0 CE1 CE2 X CM⌋ * dXi X.r ((X.S C0 CE1 CE2).bPlus - x.2.2)

def RestRankL : Prop :=
  ∀ dl ∈ clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl aTop,
    Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) ≤ rL C0 CE1 CE2 X aTop x.1 x.2

def RestPlusB (CM : ℝ) : Prop :=
  ∀ dl ∈ clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl aTop,
    (∑ aPlus ∈ X.winA, (bLvl C0 CE1 CE2 X aTop aPlus x.1 x.2 ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℝ)) ≤
      (X.winA.card : ℝ) *
        ((Formalism.GM.M.bad X.p (bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2)
            (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) ⌊D1r C0 CE1 CE2 X CM⌋ : ℝ) +
          5 / X.L.Y * (Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) : ℝ))

variable {C0 CE1 CE2 X}

theorem restPlus_of (CM : ℝ) (hY : 0 < X.L.Y) (hA : RestPlusA C0 CE1 CE2 X CM) (hR : RestRankL C0 CE1 CE2 X)
    (hB : RestPlusB C0 CE1 CE2 X CM) : RestPlus C0 CE1 CE2 X CM := by
  intro dl hdl aTop haTop x hx
  have hA' := hA dl hdl aTop haTop x hx
  have hR' := hR dl hdl aTop haTop x hx
  refine (hB dl hdl aTop haTop x hx).trans ?_
  refine mul_le_mul_of_nonneg_left (add_le_add (by exact_mod_cast hA') ?_) (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hR') (div_nonneg (by norm_num) hY.le)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
