module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PsiLocConductorEventually
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.UG

namespace GlobalTheory.RamShift

variable {E : Type} [Field E] [NumberField E]

def CondOne (w : HeightOneSpectrum (𝓞 E)) (c : w.adicCompletion E) : Prop :=
  ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (c * x * y))) : ℂ) = 1) ↔ x ∈ Ov E w


open Classical in
def condExp (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (w : HeightOneSpectrum (𝓞 E)) : ℤ :=
  if CondOne w 1 then 0
  else if h : ∃ k : ℤ, CondOne w ((ϖ w ^ k : (w.adicCompletion E)ˣ) : w.adicCompletion E) then h.choose else 0


variable (E) in
def badSet : Finset (HeightOneSpectrum (𝓞 E)) := (GlobalTheory.JSW.psiLoc_conductor_eventually E).choose

theorem condOne_one_of_notMem {w : HeightOneSpectrum (𝓞 E)} (hw : w ∉ badSet E) : CondOne w 1 := by
  intro x
  simp only [one_mul]
  exact (GlobalTheory.JSW.psiLoc_conductor_eventually E).choose_spec w hw x

theorem condExp_eq_zero_of_notMem (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    {w : HeightOneSpectrum (𝓞 E)} (hw : w ∉ badSet E) : condExp ϖ w = 0 := by
  classical
  rw [condExp, if_pos (condOne_one_of_notMem hw)]


open Classical in
def shiftFn (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E))) (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (w : HeightOneSpectrum (𝓞 E)) : Fin (m + 1) → ℤ :=
  if w ∈ T then 0 else fun i : Fin (m + 1) => condExp ϖ w * ((m : ℤ) - ((i : ℕ) : ℤ))

theorem shiftFn_mem_badSet (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (w : HeightOneSpectrum (𝓞 E))
    (h : shiftFn m T ϖ w ≠ 0) : w ∈ badSet E := by
  classical
  by_contra hw
  apply h
  unfold shiftFn
  split_ifs
  · rfl
  · funext i
    simp [condExp_eq_zero_of_notMem ϖ hw]


open Classical in
def shift (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E))) (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) :
    GlobalTheory.CellDec.abelian₂ E (m + 1) T :=
  ⟨Finsupp.onFinset (badSet E) (shiftFn m T ϖ) (shiftFn_mem_badSet m T ϖ), fun w hw => by
    rw [Finsupp.onFinset_apply, shiftFn, if_pos hw]⟩

theorem shift_apply (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (w : HeightOneSpectrum (𝓞 E)) :
    (shift m T ϖ).1 w = shiftFn m T ϖ w := by
  classical
  simp only [shift, Finsupp.onFinset_apply]

theorem shift_apply_of_notMem (m : ℕ) {T : Finset (HeightOneSpectrum (𝓞 E))}
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) {w : HeightOneSpectrum (𝓞 E)} (hw : w ∉ T) :
    (shift m T ϖ).1 w = fun i : Fin (m + 1) => condExp ϖ w * ((m : ℤ) - ((i : ℕ) : ℤ)) := by
  classical
  rw [shift_apply, shiftFn, if_neg hw]

theorem shift_last (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (w : HeightOneSpectrum (𝓞 E)) :
    (shift m T ϖ).1 w (Fin.last m) = 0 := by
  classical
  rw [shift_apply, shiftFn]
  split_ifs
  · rfl
  · simp

end GlobalTheory.RamShift
