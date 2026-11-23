module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

@[expose] public section

noncomputable section

namespace GlobalTheory.RowModelRoad

open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.BlockComplement GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple

section Twist

variable {Γ O : Type} [Group Γ] [CommRing O] {n : ℕ}

end Twist

section Lift

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

end Lift

section Eig

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (A : NAut N) (i : N.Loc)

theorem frobEig_block (θ : A.CG 1) (t : ℕ) (w : PlE H) (b : ℂ) (hu : A.unr (A.locG θ w))
    (hb : A.frobEig (A.locG θ w) = {b}) :
    A.unr (spehLoc N A ⟨1, θ, t⟩ w) ∧ A.frobEig (spehLoc N A ⟨1, θ, t⟩ w) =
      ((List.range t : List ℕ) : Multiset ℕ).map
        fun k : ℕ => b * ((normV w : ℕ) : ℂ) ^ (((((t : ℝ) - 1) / 2 - k : ℝ)) : ℂ) := by
  unfold spehLoc
  dsimp only
  induction List.range t with
  | nil => exact ⟨A.lpZero_unr w, by simp [A.frobEig_zero]⟩
  | cons k l ih =>
    have h1 := (A.unr_tw _ (((t : ℝ) - 1) / 2 - k)).2 hu
    refine ⟨(A.unr_sum _ _).2 ⟨h1, ih.1⟩, ?_⟩
    refine (A.frobEig_sum _ _ h1 ih.1).trans ?_
    rw [ih.2, A.frobEig_tw _ _ hu, hb]
    simp

end Eig

variable {D : D7}

end GlobalTheory.RowModelRoad
