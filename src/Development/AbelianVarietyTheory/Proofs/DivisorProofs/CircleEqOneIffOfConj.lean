module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilGramSignature
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift

namespace GlobalTheory.GalLift

theorem circle_eq_one_iff_of_conj {K L : Type} [Field K] [Field L] [Algebra K L] (s t : L →+* ℂ) (a b : Circle) (y : K)
    (ha : (a : ℂ) = s (algebraMap K L y)) (hb : (b : ℂ) = t (algebraMap K L y)) : b = 1 ↔ a = 1 := by
  rw [← Circle.coe_eq_one, ← Circle.coe_eq_one, ha, hb, map_eq_one_iff t t.injective, map_eq_one_iff s s.injective]

theorem logHookSum_of_bijective {D : D7} (i : Fin D.R.m) (l : D.what₂.Tau → D.what₂.Tau) (hl : Function.Bijective l) :
    logHookSum i l = logHookSum i id := by
  have hs : ∀ ρ, (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) :=
    fun ρ => D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _
  unfold logHookSum
  simp only [pW, qW, hs, id]
  exact hl.sum_comp (fun ρ => Real.log ((hookRows (D.R.sigW ((i : ℕ) + 1)).1 (aPl D i (D.R.sigW ((i : ℕ) + 1)).1 ρ) *
    hookRows (D.R.sigW ((i : ℕ) + 1)).2 (aMi D i (D.R.sigW ((i : ℕ) + 1)).1 (D.R.sigW ((i : ℕ) + 1)).2 ρ) : ℕ) : ℝ))

end GlobalTheory.GalLift
