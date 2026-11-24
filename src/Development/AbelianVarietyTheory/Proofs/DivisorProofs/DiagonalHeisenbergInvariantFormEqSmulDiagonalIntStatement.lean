module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalHeisenbergInvariantFormEqSmulDiagonalInt
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.diagonalHeisenbergInvariant_form_eq_smul_diagonalIntegral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (κ : Type) [Fintype κ] (l : ((κ ⊕ κ → AF D.host.F) → ℂ) →ₗ[ℂ] ℂ),
      l ∈ (GlobalTheory.WeilM.adeleClass D.host.F).adm (κ ⊕ κ) →
      (∀ x y : κ → AF D.host.F, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ),
        l (GlobalTheory.WeilM.schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) = l Φ) →
      ∀ μ : @MeasureTheory.Measure (κ → AF D.host.F) (borel _),
        @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∃ c : ℂ, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ), l Φ = c * GlobalTheory.DiagSiegel.diagInt μ Φ := by
  first | exact @GlobalTheory.HostDiagUniq.eq_smul_diagInt | exact GlobalTheory.HostDiagUniq.eq_smul_diagInt | (intros; apply GlobalTheory.HostDiagUniq.eq_smul_diagInt <;> assumption)
