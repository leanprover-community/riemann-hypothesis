module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumAdelicReadingEqOfTwoBaseChangeDecompsOnCover
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
import Mathlib.Tactic.NormNum.Prime
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.sum_adelicReading_eq_of_two_baseChange_decomps_on_cover : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (C : Cover T j σ), C.σ₂.comp C.inc = σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (m m' : ℕ) (x : Fin m → C.c'.F) (f : Fin m → T.R j) (as : Fin m' → C.c'.F) (fs : Fin m' → T.R j), (∀ b, f b ∈ sec (T.Q.Xo j) T.Q.c a n) → IsBC C.hle (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) as fs → ∑ b, C.σ₂ (C.d.eF (x b)) • T.phiJ j σ a (f b) = ∑ i, C.σ₂ (C.d.eF (as i)) • T.phiJ j σ a (fs i) := by
  first | exact @GlobalTheory.CoverBCRead.phiJ_sum_eq_of_isBC | exact GlobalTheory.CoverBCRead.phiJ_sum_eq_of_isBC | (intros; apply GlobalTheory.CoverBCRead.phiJ_sum_eq_of_isBC <;> assumption)
