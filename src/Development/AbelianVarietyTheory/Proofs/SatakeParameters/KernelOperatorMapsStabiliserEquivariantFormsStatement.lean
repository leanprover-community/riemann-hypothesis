module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsAre
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelOperatorMapsStabiliserEquivariantForms
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

theorem _root_.GlobalTheory.T.kernelOperator_maps_stabiliserEquivariant_forms : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (A : ColumnsAtT D.R C) (Pm : PeriodMap D.R C) (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm) (O : GL3Theta.LiftObj D C) (G : StabDat C), FormsAre M O G → (∀ i < D.R.m, UnfIs O i (nuT D u i)) → (∀ i < D.R.m, ∀ c c', Differentiable ℂ (O.Th i c c')) → (∀ i < D.R.m, ∀ c c', ∀ g ∈ G (i + 1) c', TermLaw O i c c' g) → ∀ i < D.R.m, ∀ φ ∈ M.Fi i, C.K i φ ∈ M.Fi (i + 1) := by
  first | exact @GlobalTheory.KerJ.FiCore.K_mem_Fi | exact GlobalTheory.KerJ.FiCore.K_mem_Fi | (intros; apply GlobalTheory.KerJ.FiCore.K_mem_Fi <;> assumption)
