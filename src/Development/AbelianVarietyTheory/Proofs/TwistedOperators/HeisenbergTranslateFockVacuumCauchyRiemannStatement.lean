module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergTranslateFockVacuumCauchyRiemann
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjMono

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

theorem _root_.GlobalTheory.T.heisenbergTranslate_fockVacuum_cauchyRiemann : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (f : WO S T → ℂ), GlobalTheory.ChainFr.IsVacF ψ θ A B f → ∀ y : WO S T, Differentiable ℝ (fun w : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S w) f y) ∧ ∀ w z : GlobalTheory.FockCompare.RW T S, fderiv ℝ (fun w : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S w) f y) w z + Complex.I * fderiv ℝ (fun w : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S w) f y) w (GlobalTheory.VacUnique.jO S T A.cart B.cart z) = (Real.pi : ℂ) * Complex.I * ((GlobalTheory.VacUnique.omO S T w z : ℂ) + Complex.I * (GlobalTheory.VacUnique.omO S T w (GlobalTheory.VacUnique.jO S T A.cart B.cart z) : ℂ)) * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S w) f y := by
  first | exact @GlobalTheory.HeisTranslCR.heis_translate_cauchy_riemann | exact GlobalTheory.HeisTranslCR.heis_translate_cauchy_riemann | (intros; apply GlobalTheory.HeisTranslCR.heis_translate_cauchy_riemann <;> assumption)
