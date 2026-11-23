module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCombinationRebaseVacuumLatticesInjective
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_combination_rebase_vacuumLattices_injective : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M N : GlobalTheory.FinPl.Lat S) (M' N' : GlobalTheory.FinPl.Lat T) (Q : Finset (GlobalTheory.FinPl.Pl D)), IsSelfDualC S M → IsSelfDualC S N → IsSelfDualC T M' → IsSelfDualC T N' → (∀ p ∈ Q, ((∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D p ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧ (∀ a ∈ GlobalTheory.FinPl.intAt D (· = p), incA D D.host.xi0 * a ∈ GlobalTheory.FinPl.intAt D (· = p) ∧ incA D D.host.xi0⁻¹ * a ∈ GlobalTheory.FinPl.intAt D (· = p)) ∧ ∀ (V : HSp D) (Λ : GlobalTheory.FinPl.Lat V), GlobalTheory.FinPl.latA V Λ (· = p) = GlobalTheory.FinPl.latV V Λ (· = p))) → (∀ p, p ∉ Q → GlobalTheory.FinPl.latV S M (· = p) = GlobalTheory.FinPl.latV S N (· = p) ∧ GlobalTheory.FinPl.latV T M' (· = p) = GlobalTheory.FinPl.latV T N' (· = p)) → ∃ o : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt (· ∈ Q) o ∧ ∀ f, GlobalTheory.FinPl.Vac ψ S T M M' (fun _ => True) f → GlobalTheory.FinPl.Vac ψ S T N N' (fun _ => True) (comb ψ S T o f) ∧ (f ≠ 0 → comb ψ S T o f ≠ 0) := by
  first | exact @GlobalTheory.VacRebase.rebase_vac | exact GlobalTheory.VacRebase.rebase_vac | (intros; apply GlobalTheory.VacRebase.rebase_vac <;> assumption)
