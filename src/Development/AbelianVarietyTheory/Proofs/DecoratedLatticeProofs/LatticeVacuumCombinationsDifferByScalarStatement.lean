module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeVacuumCombinationsDifferByScalar
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

theorem _root_.GlobalTheory.T.latticeVacuumCombinations_differ_by_scalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (M N : GlobalTheory.FinPl.Lat S) (M' N' : GlobalTheory.FinPl.Lat T) (Q : Finset (GlobalTheory.FinPl.Pl D)) (o o' : WO S T →₀ ℂ) (g₀ : WO S T → ℂ), IsStdChar D ψ (-1) → IsSelfDualC S M → IsSelfDualC T M' → IsSelfDualC S N → IsSelfDualC T N' → GlobalTheory.FinPl.CombAt (· ∈ Q) o → GlobalTheory.FinPl.CombAt (· ∈ Q) o' → GlobalTheory.FinPl.Vac ψ S T M M' (· ∈ Q) g₀ → GlobalTheory.FinPl.Vac ψ S T N N' (· ∈ Q) (comb ψ S T o g₀) → GlobalTheory.FinPl.Vac ψ S T N N' (· ∈ Q) (comb ψ S T o' g₀) → comb ψ S T o' g₀ ≠ 0 → ∃ c : ℂ, comb ψ S T o g₀ = c • comb ψ S T o' g₀ := by
  first | exact @GlobalTheory.VacScalar.main | exact GlobalTheory.VacScalar.main | (intros; apply GlobalTheory.VacScalar.main <;> assumption)
