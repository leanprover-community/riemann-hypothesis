module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua : ∀ (D : D7) (P : Pl D → Prop), (∃ ε : AE D, ε * ε = ε ∧ cA D ε = ε ∧ ε ∈ intAt D P ∧ (∀ a, a ∈ idAt D P ↔ ε * a = a) ∧ (∀ a, a ∈ idOff D P ↔ ε * a = 0)) ∧ ∀ S : HSp D, (∀ h : GA D S, ∃ x ∈ grpAt S P, ∃ y ∈ grpOff S P, h = x * y) ∧ (∀ x ∈ grpAt S P, ∀ y ∈ grpOff S P, x * y = y * x) ∧ grpAt S P ⊓ grpOff S P = ⊥ ∧ (∀ (L : Lat S) (y : Fin S.rank → AE D), (Submodule.IsLattice D.host.E L) → (y ∈ latV S L P ↔ (∀ i, y i ∈ idAt D P) ∧ ∀ v, P v → ∀ e ∈ intAt D (· = v), e • y ∈ latV S L (· = v))) := by
  first | exact @GlobalTheory.FinPl.localComponents | exact GlobalTheory.FinPl.localComponents | (intros; apply GlobalTheory.FinPl.localComponents <;> assumption)
