module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GoodLoc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelLinearMapMatrixExists
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

theorem _root_.GlobalTheory.T.besselModel_linearMap_matrix_exists : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (τ : D.what₂.Tau) (m : (VS D).V →ₗ[D.host.E] (VS D).V),
    ∃ n : MatKR D.R.k D.R.rS, ∀ y, n *ᵥ GlobalTheory.TypeAsm.phiV C τ y = GlobalTheory.TypeAsm.phiV C τ (m y) := by
  first | exact @GlobalTheory.TypeAsm.phiV_linMat_all | exact GlobalTheory.TypeAsm.phiV_linMat_all | (intros; apply GlobalTheory.TypeAsm.phiV_linMat_all <;> assumption)
