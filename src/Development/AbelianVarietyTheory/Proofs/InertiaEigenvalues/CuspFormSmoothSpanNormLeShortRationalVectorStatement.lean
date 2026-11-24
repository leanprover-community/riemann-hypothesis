module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MemL2OfSmoothVector
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormSmoothSpanNormLeShortRationalVector
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

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

theorem _root_.GlobalTheory.T.cuspFormSmoothSpan_norm_le_shortRationalVector : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (π : CuspSub E a), π.IsUnitary → ∀ φ : Sm E a, (φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) → ∀ l : List (Lie E a),
    ∀ L : Set (Fin a → Af E), IsCompact L → ∀ C₀ : Set (GA E a), IsCompact C₀ → ∀ N : ℕ, ∃ C : ℝ,
      ∀ g : GA E a, ∀ c ∈ C₀, ∀ ξ : Fin a → E, ξ ≠ 0 →
        (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i)) ∈ L →
          ‖(GlobalTheory.GLFin.word l φ).1 (g * c)‖ ≤
            C * (‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i)‖ ^ (a * Module.finrank ℚ E) /
              (ideleModule E (GeneralLinearGroup.det g) : ℝ)) ^ N := by
  first | exact @GlobalTheory.MSpanDecay.norm_le_of_short_vector_mspanR | exact GlobalTheory.MSpanDecay.norm_le_of_short_vector_mspanR | (intros; apply GlobalTheory.MSpanDecay.norm_le_of_short_vector_mspanR <;> assumption)
