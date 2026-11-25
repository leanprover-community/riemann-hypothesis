module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
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

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
noncomputable section

namespace GlobalTheory.BCT.LocVal

theorem cj_algebraMap {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (hw : ¬ IsSplitAt w) (x : E) :
    cj w (algebraMap E (w.adicCompletion E) x) = algebraMap E (w.adicCompletion E) (IsCMField.complexConj E x) := by
  have key : ∀ u : Pl E, u = w → ∀ f : u.adicCompletion E →+* w.adicCompletion E, Continuous f →
      (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (IsCMField.complexConj E k)) →
      ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
        ∀ k : E, s (algebraMap E _ k) = algebraMap E _ (IsCMField.complexConj E k) := by
    intro u hu f hf hk
    subst hu
    exact ⟨f, hf, hk⟩
  have hex := key _ ((GlobalTheory.ConjAtPlace.conjSrc_eq_iff w).2 hw) (GlobalTheory.CuspRep.conjLoc ((IsCMField.complexConj E).toRingEquiv) w)
    (GlobalTheory.CuspRep.conjLoc_spec _ w).1 (GlobalTheory.CuspRep.conjLoc_spec _ w).2.1
  unfold cj
  rw [dite_eq_left hex]
  exact hex.choose_spec.2 x

theorem map_mem_UL {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (γ : UE E n) (w : Pl E) :
    Matrix.GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (γ : GL (Fin n) E) ∈ UL n w := by
  unfold UL
  split_ifs with hw
  · exact Subgroup.mem_top _
  · have hγ : cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ : GL (Fin n) E).val * 1 * (γ : GL (Fin n) E).val = 1 :=
      γ.2
    change cT (cj w) ((algebraMap E (w.adicCompletion E)).mapMatrix (γ : GL (Fin n) E).val) * 1 *
      (algebraMap E (w.adicCompletion E)).mapMatrix (γ : GL (Fin n) E).val = 1
    have e : cT (cj w) ((algebraMap E (w.adicCompletion E)).mapMatrix (γ : GL (Fin n) E).val) =
        (algebraMap E (w.adicCompletion E)).mapMatrix
          (cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ : GL (Fin n) E).val) := by
      ext i j
      simp [cT, Matrix.map_apply, cj_algebraMap w hw]
    rw [e, Matrix.mul_one, ← map_mul, ← Matrix.mul_one (cT _ _), hγ, map_one]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ (γ : UE E n) (w : Pl E),
    ((locPt w γ : UL n w) : GLw n w) = Matrix.GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (γ : GL (Fin n) E) := by
  intro E _ _ _ _ n γ w
  unfold locPt toSub
  rw [dite_eq_left (map_mem_UL γ w)]

end GlobalTheory.BCT.LocVal
