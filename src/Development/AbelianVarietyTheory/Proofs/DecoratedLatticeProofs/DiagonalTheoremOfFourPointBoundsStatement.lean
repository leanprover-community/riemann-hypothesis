module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DiagAtScale
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalTheoremOfFourPointBounds
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

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

theorem _root_.GlobalTheory.T.diagonalTheorem_of_fourPointBounds : ∀ (D : D7) (c : Formalism.L2.SG.ThmSOwn.ConcK D) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Γ₁ Γ₂ Γ : ℝ) (u : D.what₂.Word), 29 ≤ C' → 29 ≤ Cl → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → 0 ≤ Γ₁ → 0 ≤ Γ₂ → Γ₁ + Γ₂ ≤ Γ → VanishingGramTermsBound c.Y u → CollS c.Y u → (c.Y.tO u u).pairSum ((c.Y.tO u u).one (c.Y.tO u u).genSet) ≤ Γ₁ * ddC c.X c.Y u u → (c.Y.tO u u).pairSum ((c.Y.tO u u).one (c.Y.tO u u).ngSet) ≤ Γ₂ * ddC c.X c.Y u u → SDiagAt D u Γ (1 / 2) := by
  first | exact @GlobalTheory.Core.Diag.sDiagAt_of_points | exact GlobalTheory.Core.Diag.sDiagAt_of_points | (intros; apply GlobalTheory.Core.Diag.sDiagAt_of_points <;> assumption)
