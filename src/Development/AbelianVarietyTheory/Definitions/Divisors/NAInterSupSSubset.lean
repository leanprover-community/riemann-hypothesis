module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import GroundTheory.AutomorphicForms.MultiplicityOne.Equivariance
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory

namespace GlobalTheory.JSW.WhitModel

open GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem mem_NA_iff (u : GA E a) : u ∈ NA (E := E) (a := a) ↔ ∃ X : Pos a → Ad E, u = uGL X := by
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨fun p => (u : Matrix (Fin a) (Fin a) (Ad E)) p.1.1 p.1.2, Units.ext ?_⟩
    refine Matrix.ext fun i j => ?_
    rw [coe_uGL, uMat_apply]
    split_ifs with h h'
    · subst h; exact h1 i
    · rfl
    · exact h0 i j (lt_of_le_of_ne (not_lt.1 h') (Ne.symm h))
  · rintro ⟨X, rfl⟩
    refine ⟨fun i j h => ?_, fun i => ?_⟩
    · rw [coe_uGL, uMat_apply, if_neg (ne_of_gt h), dite_eq_right (not_lt.2 h.le)]
    · rw [coe_uGL, uMat_apply, if_pos rfl]

theorem superDiag_uGL (X : Pos a → Ad E) : GlobalTheory.Whittaker.superDiag (uGL X) = supSum 0 X := by
  classical
  unfold GlobalTheory.Whittaker.superDiag supSum
  refine (Finset.sum_sigma' _ _ _).trans ?_
  symm
  refine Finset.sum_bij (fun p _ => ⟨p.1.1, p.1.2⟩) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp [hp.1]
  · intro p _ q _ h
    simp only [Sigma.mk.injEq, heq_eq_eq] at h
    exact Subtype.ext (Prod.ext h.1 h.2)
  · rintro ⟨i, j⟩ h
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact ⟨⟨(i, j), by rw [Fin.lt_def]; simp only; omega⟩, by simp [h], rfl⟩
  · intro p _
    simp only [coe_uGL, uMat_apply]
    rw [if_neg (ne_of_lt p.2), dite_eq_left p.2]

theorem whit_mul {F : GA E a → ℂ} (hc : Continuous F) (hl : AutomorphicForm.IsLeftInvariant F) {u : GA E a}
    (hu : u ∈ NA (E := E) (a := a)) (g : GA E a) : whit F (u * g) = psiN u * whit F g := by
  obtain ⟨X, rfl⟩ := (mem_NA_iff u).1 hu
  rw [psiN, superDiag_uGL]
  exact MultiplicityOne.whittaker_uGL_mul hc hl X g

theorem psiLoc_eq (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E) :
    psiLoc w x = (GroundTheory.Global.localAdelicChar E w x : ℂ) := by
  classical
  rw [psiLoc, GroundTheory.Global.localAdelicChar_apply]
  congr 2

theorem loc_mem_supS (S : Finset (HeightOneSpectrum (𝓞 E))) (w : HeightOneSpectrum (𝓞 E))
    (g : GL (Fin a) (w.adicCompletion E)) : finGL E a (locGL E a w g) ∈ supS (E := E) (a := a) S ↔ w ∈ S ∨ g = 1 := by
  have hc : ∀ v, ∀ g : GA E a, GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) g =
      GeneralLinearGroup.map (pLoc E v) (GeneralLinearGroup.map (pFin E) g) := fun _ _ => rfl
  constructor
  · intro h
    by_cases hw : w ∈ S
    · exact Or.inl hw
    · have := h w hw
      rw [hc, pFin_finGL, pLoc_locGL] at this
      exact Or.inr this
  · rintro (h | rfl) v hv
    · rw [hc, pFin_finGL, pLoc_locGL_of_ne (fun e : v = w => hv (by rw [e]; exact h))]
    · simp

variable [_root_.NumberField.IsTotallyComplex E]

end GlobalTheory.JSW.WhitModel
