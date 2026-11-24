module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualFor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeIndicatorFourier
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.local_lattice_indicator_fourier : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (v : Pl (F := F)) (κ : Type) [Fintype κ],
    GlobalTheory.SympChange.indO (κ := κ) v ∈ SB (κ → Fv F v) ∧
    (PsiUnr ψ v → fourV ψ v (GlobalTheory.SympChange.indO (κ := κ) v) = GlobalTheory.SympChange.indO v) := by
  first | exact @GlobalTheory.WeylFour.IndOSelf.indO_self_fourier | exact GlobalTheory.WeylFour.IndOSelf.indO_self_fourier | (intros; apply GlobalTheory.WeylFour.IndOSelf.indO_self_fourier <;> assumption)
