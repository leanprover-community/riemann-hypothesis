module

public import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SecBCAndCuspBC
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData

@[expose] public section

noncomputable section

namespace GlobalTheory.PhRatCommon

section Lemmas

open NumberField
open scoped TensorProduct

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AdTh

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {r : ℕ}

theorem rdU_of_isBC (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) {m : ℕ} {f' : Rul Xo c'} {as : Fin m → c'.F}
    {fs : Fin m → Rul Xo c} (h : IsBC hle f' as fs) (k : (U (σ'.comp (incF c c' hle))).Comp)
    (x : Frame ((U (σ'.comp (incF c c' hle))).X k).Ψ r) :
    rdU (unfBC hle U σ') f' k x = ∑ j, σ' (as j) * rdU (U (σ'.comp (incF c c' hle))) (fs j) k x := by
  by_cases hx : x ∈ ((U (σ'.comp (incF c c' hle))).X k).dom
  · letI : Algebra c.F (CAt σ') := (σ'.comp (incF c c' hle)).toAlgebra
    have e := h (CAt σ') (fun _ => rfl) ((unfBC hle U σ').un k ⟨x, hx⟩)
    have e1 : rdU (unfBC hle U σ') f' k x = toC (evR Xo c' f' ((unfBC hle U σ').un k ⟨x, hx⟩)) := dif_pos hx
    rw [e1, e]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e2 : rdU (U (σ'.comp (incF c c' hle))) (fs j) k x =
      toC (evR Xo c (fs j) ((U (σ'.comp (incF c c' hle))).un k ⟨x, hx⟩)) := dif_pos hx
    rw [e2]
    rfl
  · have e1 : rdU (unfBC hle U σ') f' k x = 0 := dif_neg hx
    rw [e1]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    have e2 : rdU (U (σ'.comp (incF c c' hle))) (fs j) k x = 0 := dif_neg hx
    rw [e2, mul_zero]

theorem exists_rdU_eq_sum (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (f' : Rul Xo c') (hf : f' ∈ cusp Xo c' (unfBC hle U) a n) :
    ∃ (m : ℕ) (b : Fin m → c'.F) (fs : Fin m → cusp Xo c U a n), ∀ k x,
      rdU (unfBC hle U σ') f' k x = ∑ j, σ' (b j) * rdU (U (σ'.comp (incF c c' hle))) (fs j : Rul Xo c) k x := by
  obtain ⟨m, b, fs, hfs, hbc⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC E H Dw l Xo c c' hle).2 r U a n f' hf
  exact ⟨m, b, fun j => ⟨fs j, hfs j⟩, rdU_of_isBC hle U σ' hbc⟩

end Gen

theorem sum_shape {m : ℕ} {c l u x : ℂ} {a a' y p : Fin m → ℂ} (h : x = ∑ j, a j * y j) (ha : ∀ j, a' j = a j)
    (hp : ∀ j, p j = c * u * y j) : c * l * u * x = ∑ j, a' j * (l * p j) := by
  rw [h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ha, hp]
  ring

end Lemmas

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate

end GlobalTheory.PhRatCommon
