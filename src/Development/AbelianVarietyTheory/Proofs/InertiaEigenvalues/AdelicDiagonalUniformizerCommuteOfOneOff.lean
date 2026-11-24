module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.CellDec.TlComm

theorem tl_commute_of_one_off : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (l : GlobalTheory.CellDec.abelian₂ E n S) (p : GA E n),
    (∀ w ∉ S, Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p = 1) →
    p * GlobalTheory.CellDec.tl n ϖ l.1 = GlobalTheory.CellDec.tl n ϖ l.1 * p := by
  intro E _ _ n S ϖ l p hp
  have key : ∀ {R : Type} [CommRing R] (c : Ad E →+* R),
      (Matrix.GeneralLinearGroup.map c p = 1 ∨ Matrix.GeneralLinearGroup.map c (GlobalTheory.CellDec.tl n ϖ l.1) = 1) →
      Matrix.GeneralLinearGroup.map c (p * GlobalTheory.CellDec.tl n ϖ l.1) =
        Matrix.GeneralLinearGroup.map c (GlobalTheory.CellDec.tl n ϖ l.1 * p) := by
    intro R _ c h
    rw [map_mul, map_mul]
    rcases h with h | h <;> rw [h] <;> simp
  refine GlobalTheory.JSW.GA_ext (key _ (Or.inr ?_)) fun v => key _ ?_
  · exact map_cornerGL_of_zero _ _ (fun x => rfl) _
  · by_cases hv : v ∈ S
    · refine Or.inr ?_
      rw [GlobalTheory.CellDec.tl, finGL, map_cornerGL_of_hom (sFin E) ((pLoc E v).comp (pFin E)) (pLoc E v) (fun x => rfl)]
      refine Matrix.GeneralLinearGroup.ext fun i j => ?_
      rw [Matrix.GeneralLinearGroup.map_apply, GlobalTheory.SmGL.val_diagT]
      have hl : l.1 v = 0 := l.2 v hv
      by_cases hij : i = j
      · subst hij
        rw [Matrix.diagonal_apply_eq, Units.val_one, Matrix.one_apply_eq]
        show ((ϖ v ^ ((Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l.1) v) : (v.adicCompletion E)ˣ) :
          v.adicCompletion E) = 1
        rw [Finsupp.mapRange_apply, hl, Pi.zero_apply, zpow_zero, Units.val_one]
      · simp [hij]
    · exact Or.inl (hp v hv)

end GlobalTheory.CellDec.TlComm
