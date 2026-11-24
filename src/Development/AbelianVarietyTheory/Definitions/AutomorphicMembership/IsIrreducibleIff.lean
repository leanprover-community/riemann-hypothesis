module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
public import Mathlib.RepresentationTheory.Irreducible
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Topology

namespace GlobalTheory.CuspRep

variable {G : Type} [Group G]

theorem isIrreducible_iff {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) :
    ρ.IsIrreducible ↔ Nontrivial V ∧ ∀ W : Submodule ℂ V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  constructor
  · intro h
    refine ⟨?_, fun W hW => ?_⟩
    · have : (⊥ : Submodule ℂ V) ≠ ⊤ := fun e =>
        bot_ne_top (α := Subrepresentation ρ) (Subrepresentation.toSubmodule_injective e)
      exact (Submodule.nontrivial_iff ℂ).1 ⟨⟨_, _, this⟩⟩
    · exact (eq_bot_or_eq_top (⟨W, hW⟩ : Subrepresentation ρ)).imp (congrArg Subrepresentation.toSubmodule)
        (congrArg Subrepresentation.toSubmodule)
  · rintro ⟨h0, h⟩
    have : Nontrivial (Subrepresentation ρ) :=
      ⟨⟨⊥, ⊤, fun e => bot_ne_top (congrArg Subrepresentation.toSubmodule e : (⊥ : Submodule ℂ V) = ⊤)⟩⟩
    exact ⟨fun W => (h W.toSubmodule W.apply_mem_toSubmodule).imp
      (fun e => Subrepresentation.toSubmodule_injective e) (fun e => Subrepresentation.toSubmodule_injective e)⟩

@[simp] theorem twRep_apply {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (χ : G →* ℂˣ)
    (g : G) (v : V) : twRep ρ χ g v = ((χ g : ℂˣ) : ℂ) • ρ g v := rfl

variable [TopologicalSpace G]


variable (G) in
structure SmIrr (G : Type) [Group G] [TopologicalSpace G] where

  V : Type
  [acg : AddCommGroup V]
  [mod : Module ℂ V]

  ρ : Representation ℂ G V
  smooth : GlobalTheory.PRep.IsSmooth ρ
  irred : ρ.IsIrreducible

attribute [instance] SmIrr.acg SmIrr.mod


variable (G) in
instance SmIrr.setoid : Setoid (SmIrr G) where
  r σ σ' := Nonempty (σ.ρ.Equiv σ'.ρ)
  iseqv := ⟨fun σ => ⟨.refl σ.ρ⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩⟩


variable (G) in
def Irr (G : Type) [Group G] [TopologicalSpace G] : Type 1 := Quotient (@SmIrr.setoid G _ _)


variable (G) in
def SmIrr.triv : SmIrr G where
  V := ℂ
  ρ := Representation.trivial ℂ G ℂ
  smooth v := by simp
  irred := (isIrreducible_iff _).2 ⟨inferInstance, fun W _ => eq_bot_or_eq_top W⟩

instance : Inhabited (Irr G) := ⟨Quotient.mk (@SmIrr.setoid G _ _) (SmIrr.triv G)⟩

variable [IsTopologicalGroup G]

def SmIrr.twist (σ : SmIrr G) (χ : G →* ℂˣ) (hχ : IsOpen {g | χ g = 1}) : SmIrr G where
  V := σ.V
  ρ := twRep σ.ρ χ
  smooth v := isOpen_stab_of_mem_nhds _ v <| Filter.mem_of_superset
    (((σ.smooth v).inter hχ).mem_nhds ⟨by simp, by simp⟩) fun g hg => by
      have h1 : σ.ρ g v = v := hg.1
      have h2 : χ g = 1 := hg.2
      simp [h1, h2]
  irred := by
    obtain ⟨h0, h⟩ := (isIrreducible_iff _).1 σ.irred
    refine (isIrreducible_iff _).2 ⟨h0, fun W hW => h W fun g v hv => ?_⟩
    exact (W.smul_mem_iff (Units.ne_zero (χ g))).1 (hW g v hv)

def Irr.twist (σ : Irr G) (χ : G →* ℂˣ) (hχ : IsOpen {g | χ g = 1}) : Irr G :=
  Quotient.map (sa := @SmIrr.setoid G _ _) (sb := @SmIrr.setoid G _ _) (fun σ : SmIrr G => σ.twist χ hχ) (fun σ σ' ⟨e⟩ => ⟨.mk e.toLinearEquiv fun g => by
    ext v
    change e (((χ g : ℂˣ) : ℂ) • σ.ρ g v) = ((χ g : ℂˣ) : ℂ) • σ'.ρ g (e v)
    rw [map_smul]
    exact congrArg _ (LinearMap.congr_fun (e.isIntertwining' g) v)⟩) σ

def Irr.ofChar (χ : G →* ℂˣ) (hχ : IsOpen {g | χ g = 1}) : Irr G :=
  Quotient.mk (@SmIrr.setoid G _ _) ((SmIrr.triv G).twist χ hχ)

end GlobalTheory.CuspRep
