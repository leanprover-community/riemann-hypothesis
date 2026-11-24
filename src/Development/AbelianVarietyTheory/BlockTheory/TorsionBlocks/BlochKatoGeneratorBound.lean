module

public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Mathlib.Algebra.Module.Torsion.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section Reduction

variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

def latAct (L : Lattice (O := O) ρ) (g : G) : ↥L.T →ₗ[O] ↥L.T :=
  ((ρ g).restrictScalars O).restrict (fun x hx => L.stable g x hx)

abbrev LatMod (L : Lattice (O := O) ρ) (I : Ideal O) : Type :=
  ↥L.T ⧸ (I • (⊤ : Submodule O ↥L.T))

def latModAct (L : Lattice (O := O) ρ) (I : Ideal O) (g : G) : LatMod L I →ₗ[O] LatMod L I :=
  Submodule.mapQ _ _ (latAct L g) (by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top)

def galoisLatticeModIdealInvariants (L : Lattice (O := O) ρ) (I : Ideal O) : Submodule (O ⧸ I) (LatMod L I) where
  carrier := {y | ∀ g : G, latModAct L I g y = y}
  zero_mem' := fun g => map_zero _
  add_mem' := by
    intro a b ha hb g
    rw [map_add (f := _), ha g, hb g]
  smul_mem' := by
    intro c y hy g
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    change latModAct L I g (a • y) = a • y
    rw [map_smul, hy g]


variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V} in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions.mk_mem_H0Mod (L : _root_.Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ) (I : Ideal O)
    (x : ↥L.T) :
    (Submodule.Quotient.mk x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions.LatMod L I) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions.galoisLatticeModIdealInvariants L I ↔
      ∀ g : G, _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions.latAct L g x - x ∈ I • (⊤ : Submodule O ↥L.T) := by
  change (∀ g : G, _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions.latModAct L I g (Submodule.Quotient.mk x) =
    Submodule.Quotient.mk x) ↔ _
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions.latModAct, Submodule.mapQ_apply, Submodule.Quotient.eq]

def h0ModResidueDim (L : Lattice (O := O) ρ) (ϖ : O) : ℕ :=
  Module.finrank (O ⧸ Ideal.span {ϖ}) ↥(galoisLatticeModIdealInvariants L (Ideal.span {ϖ}))


variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V} in
omit [Algebra O LL] [IsScalarTower O LL V] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions.finite_latMod (L : _root_.Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ) (I : Ideal O) :
    Module.Finite (O ⧸ I) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions.LatMod L I) := by
  haveI : Module.Finite O ↥L.T := Module.Finite.iff_fg.mpr L.fg
  exact Module.Finite.of_restrictScalars_finite O (O ⧸ I) _

end Reduction

def GeneratedByAtMost {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (N : Submodule O M) (m : ℕ) : Prop :=
  ∃ s : Finset M, Submodule.span O (s : Set M) = N ∧ s.card ≤ m

section Bound

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]

end Bound

end GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions
