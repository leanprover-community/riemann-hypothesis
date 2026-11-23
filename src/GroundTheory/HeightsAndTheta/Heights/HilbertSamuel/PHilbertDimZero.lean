module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem mixedDiff_zero {K : Type*} (h : (K → ℤ) → ℤ) (bs : Fin 0 → K → ℤ) :
    mixedDiff bs h = h := by
  simp [mixedDiff]

theorem relDim_eq_zero_of_ringKrullDim {F : Type*} [Field F] {K : Type} [Fintype K]
    {ι : K → Type} (q : Ideal (MRing ι F))
    (hd : ringKrullDim (MRing ι F ⧸ q) = ((Fintype.card K : ℕ) : WithBot ℕ∞)) :
    GroundTheory.Heights₂.Heights.FieldNumbers.relDim q = ((0 : ℕ) : WithBot (WithTop ℤ)) := by
  unfold GroundTheory.Heights₂.Heights.FieldNumbers.relDim
  rw [hd]
  simp
  change WithTop.map (fun e : ℕ => (e : ℤ) - (Fintype.card K : ℤ))
    ((Fintype.card K : ℕ) : WithTop ℕ) = 0
  exact congrArg WithTop.some (sub_self _)

theorem HilbertDimZero.proof : HilbertDimZero.Statement.{u} := by
  intro F _ K _ _ ι _ q hq hd
  have h0 := ((GroundTheory.Heights₂.Heights.FieldNumbers.MixedDiffConst.full.{u} F K ι q hq.multiHomog
    hq.relevant 0 (relDim_eq_zero_of_ringKrullDim q hd)).1 (![] : Fin 0 → K → ℤ))
  simp only [mixedDiff_zero] at h0
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.1 h0
  refine ⟨Finset.univ.sup fun k => (b k).toNat, fun a ha => hb _ fun k => ?_⟩
  have h1 : (b k).toNat ≤ a k :=
    le_trans (Finset.le_sup (f := fun k => (b k).toNat) (Finset.mem_univ k)) (ha k)
  have h2 : b k ≤ ((b k).toNat : ℤ) := Int.self_le_toNat (b k)
  show b k ≤ (a k : ℤ)
  omega

end GroundTheory.Heights₂.Heights.HilbertSamuel
