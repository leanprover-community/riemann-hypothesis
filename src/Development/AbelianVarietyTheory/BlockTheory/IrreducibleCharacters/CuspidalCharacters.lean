module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ImportsAlt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspidalCharacters

open Matrix

theorem isIrreducible_iff {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) :
    ρ.IsIrreducible ↔ Nontrivial V ∧
      ∀ U : Submodule ℂ V, (∀ g : G, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤ := by
  first
  | exact @_root_.GlobalTheory.UnimodularLatticeExistence.main
  | exact _root_.GlobalTheory.UnimodularLatticeExistence.main
  | (apply _root_.GlobalTheory.UnimodularLatticeExistence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnimodularLatticeExistence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnimodularLatticeExistence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnimodularLatticeExistence.main ..)

end GlobalTheory.IndefiniteRowSideFullHecke.CuspidalCharacters
