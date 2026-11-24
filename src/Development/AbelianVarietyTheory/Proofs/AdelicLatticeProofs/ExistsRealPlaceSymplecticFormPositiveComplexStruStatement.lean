module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRealPlaceSymplecticFormPositiveComplexStru
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_realPlace_symplecticForm_positiveComplexStructure : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∃ (om : GlobalTheory.FockCompare.RW T S →ₗ[ℝ] GlobalTheory.FockCompare.RW T S →ₗ[ℝ] ℝ) (J : GlobalTheory.FockCompare.RW T S →ₗ[ℝ] GlobalTheory.FockCompare.RW T S), (∀ x y : WO S T, y.map (finPart D) = 0 → ψ (symplOH S T x y) = Complex.exp (-(Real.pi * Complex.I) * (om (GlobalTheory.FockCompare.piW θ T S x) (GlobalTheory.FockCompare.piW θ T S y) : ℝ))) ∧ (∀ z τ, J z τ = cplxO (sS τ) (sT τ) (z τ)) ∧ (∀ v, om v v = 0) ∧ (∀ v, J (J v) = -v) ∧ (∀ x y, om x (J y) = om y (J x)) ∧ ∀ v, v ≠ 0 → 0 < om v (J v) := by
  first | exact @GlobalTheory.OrientedRealForm.exists_real_form | exact GlobalTheory.OrientedRealForm.exists_real_form | (intros; apply GlobalTheory.OrientedRealForm.exists_real_form <;> assumption)
