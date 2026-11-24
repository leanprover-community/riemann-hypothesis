module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CondExpEqZeroOfNotMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocFacOfNeg
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerMulTorusShiftAddEqSphericalProduct
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun
open scoped Classical

theorem _root_.GlobalTheory.T.whittaker_mul_torusShift_add_eq_sphericalProduct : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (π : CuspSub E (m + 1)) (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂˣ),
    (∀ w, HasSatGL w.1 (π.locRep w.1) (Finset.univ.val.map (α w))) →
    ∀ φ ∈ π.V, (∀ w ∉ T, ∀ k ∈ KGL w (n := (m + 1)), act (.fin (locGL E (m + 1) w k)) φ = φ) →
    ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) T, ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T, (∀ w, 0 ≤ l.1 w (Fin.last m)) →
      GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.CellDec.tl (m + 1) ϖ ((GlobalTheory.RamShift.shift m T ϖ).1 + l.1)) =
        GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.CellDec.tl (m + 1) ϖ (GlobalTheory.RamShift.shift m T ϖ).1) *
          ∏ w ∈ l.1.support, (if h : w ∈ T then 1 else
            GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (fun i => ((α ⟨w, h⟩ i : ℂˣ) : ℂ)) (l.1 w)) := by
  first | exact @GlobalTheory.RamShift.whit_mul_tl_shift_add | exact GlobalTheory.RamShift.whit_mul_tl_shift_add | (intros; apply GlobalTheory.RamShift.whit_mul_tl_shift_add <;> assumption)
