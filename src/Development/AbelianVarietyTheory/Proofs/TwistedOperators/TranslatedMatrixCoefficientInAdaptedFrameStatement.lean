module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Adapted
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslatedMatrixCoefficientInAdaptedFrame
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.translated_matrix_coefficient_in_adapted_frame : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau)
  (B g₀' : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v₀ : M.H τ),
  IsUnit B → Bᴴ * Formalism.REAL.Jm (M.ε τ) * B = gramAt D V τ → g₀' ∈ Formalism.MainNotions.S.UJset (M.ε τ) →
  B⁻¹ * g₀' * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧
  ∀ x ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), GlobalTheory.PackLoc.mco M τ (B⁻¹ * g₀' * M.fr τ) v₀ x =
    ⟪M.σ τ g₀' v₀, M.σ τ (B * x * B⁻¹) (M.σ τ g₀' v₀)⟫_ℂ := by
  first | exact @GlobalTheory.PackLoc.mco_frame | exact GlobalTheory.PackLoc.mco_frame | (intros; apply GlobalTheory.PackLoc.mco_frame <;> assumption)
