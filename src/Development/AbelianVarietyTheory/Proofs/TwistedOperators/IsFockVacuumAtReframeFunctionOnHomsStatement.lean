module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacuumAtReframeFunctionOnHoms
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapAFrPMulFrPinv

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isFockVacuumAt_reframeFunctionOnHoms : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V), IsInfFam θ → (∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y)) → ∀ (τ : D.what₂.Tau) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ), IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 sT) f → IsFockVacAt (heisO ψ (reS S b) T) θ τ (cplxO 1 sT) (reF S T b f) := by
  first | exact @GlobalTheory.AdSpan.ReVec.FockVac.isFockVacAt_reF | exact GlobalTheory.AdSpan.ReVec.FockVac.isFockVacAt_reF | (intros; apply GlobalTheory.AdSpan.ReVec.FockVac.isFockVacAt_reF <;> assumption)
