module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatIndLastKerRow
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaSliceLineSumEqIntertwinerImage
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

theorem _root_.GlobalTheory.T.thetaSlice_lineSum_eq_intertwiner_image : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (V₀ A L S : HSp D) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : Frame p A n') (α₀ : Frame p V₀ (n' ⊕ Fin 1)) (β : Frame p S n), IsSumFrame o ζ α α₀ → ∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ), a ≠ 0 → ∀ (LS : Lat S), IsSelfDualC S LS → ∀ (L₁ : Lat V₀) (L₂ : Lat S) (f₁ Ξ : WO V₀ S → ℂ), Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ a) Ξ → ∀ u : WO A S, ∃ (g₁ : WO L S → ℂ) (T₁ : (WO L S → ℂ) →ₗ[ℂ] (WO L S → ℂ)), IsThetaFunO ψ L S g₁ ∧ IsPlaceModel ψ (symplO L S) (heisO ψ L S) p.e (latO L S ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) : Set _) (LS : Set _) (· = p.v)) 1 g₁ T₁ ∧ T₁ (colFun β ζ a) = fun y => Ξ ((o.resS S).symm (u, y)) := by
  first | exact @GlobalTheory.LastTgtSlice.main | exact GlobalTheory.LastTgtSlice.main | (intros; apply GlobalTheory.LastTgtSlice.main <;> assumption)
