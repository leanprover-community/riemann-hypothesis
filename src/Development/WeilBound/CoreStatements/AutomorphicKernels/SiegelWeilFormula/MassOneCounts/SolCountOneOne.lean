module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.MOne

open PositivityTheory.PfSWUS.Loc

theorem card_bridge {W A R : Type} [CommRing R] (ϖ : R) (a : W → A) (ha : Function.Surjective a) (φ : W → R)
    (hφ : Function.Surjective φ) (hker : ∀ w w', a w = a w' ↔ φ w - φ w' ∈ lev ϖ 1) (PA : A → Prop) (PR : R → Prop)
    (hP : ∀ w, PA (a w) ↔ PR (φ w)) :
    Nat.card {y // PA y} = Nat.card (Ideal.Quotient.mk (lev ϖ 1) '' {x | PR x}) := by
  classical
  choose s hs using ha
  let e : A → R ⧸ lev ϖ 1 := fun y => Ideal.Quotient.mk (lev ϖ 1) (φ (s y))
  have hinj : Function.Injective e := by
    intro y y' h
    have h' := Ideal.Quotient.eq.mp h
    rw [← hs y, ← hs y']
    exact (hker _ _).mpr h'
  have himg : e '' {y | PA y} = Ideal.Quotient.mk (lev ϖ 1) '' {x | PR x} := by
    ext c
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨φ (s y), ?_, rfl⟩
      have hy' : PA (a (s y)) := by
        rw [hs y]
        exact hy
      exact (hP _).mp hy'
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨w, rfl⟩ := hφ x
      refine ⟨a w, (hP w).mpr hx, ?_⟩
      exact Ideal.Quotient.eq.mpr ((hker _ _).mp (hs (a w)))
  rw [← himg, Nat.card_image_of_injective hinj]
  rfl

theorem solCount_one_one {R : Type} [CommRing R] (σ : R →+* R) (ϖ : R) (j t : R) :
    solCount σ ϖ (Matrix.of fun _ _ => j : Matrix (Fin 1) (Fin 1) R) (Matrix.of fun _ _ => t : Matrix (Fin 1) (Fin 1) R) 1 =
      Nat.card (Ideal.Quotient.mk (lev ϖ 1) '' {x : R | Ideal.Quotient.mk (lev ϖ 1) (σ x * j * x) =
        Ideal.Quotient.mk (lev ϖ 1) t}) := by
  classical
  unfold solCount
  have hinj : Function.Injective (fun y : Matrix (Fin 1) (Fin 1) (R ⧸ lev ϖ 1) => y 0 0) := by
    intro y y' h
    ext a b
    obtain rfl : a = 0 := Subsingleton.elim _ _
    obtain rfl : b = 0 := Subsingleton.elim _ _
    exact h
  rw [← Nat.card_image_of_injective hinj, Set.image_image]
  refine congrArg (fun s : Set (R ⧸ lev ϖ 1) => Nat.card s) ?_
  ext c
  constructor
  · rintro ⟨X, hX, rfl⟩
    refine ⟨X 0 0, ?_, rfl⟩
    have h00 := congrFun (congrFun hX 0) 0
    simpa [red, cT, Matrix.mul_apply] using h00
  · rintro ⟨x, hx, rfl⟩
    refine ⟨Matrix.of fun _ _ => x, ?_, rfl⟩
    simp only [Set.mem_ofPred_eq]
    ext a b
    obtain rfl : a = 0 := Subsingleton.elim _ _
    obtain rfl : b = 0 := Subsingleton.elim _ _
    simpa [red, cT, Matrix.mul_apply] using hx

end PositivityTheory.SiegelWeilFormula.MOne

end
