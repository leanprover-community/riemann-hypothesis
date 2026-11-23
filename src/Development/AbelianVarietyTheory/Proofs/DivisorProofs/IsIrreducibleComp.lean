module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlace
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCosocleComp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.DualityMap

open GlobalTheory.TypeTame

section Comp

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def compEquiv {π : Representation ℂ G V} {σ : Representation ℂ G W} (φ : π.Equiv σ) (s : H →* G) :
    Representation.Equiv (π.comp s : Representation ℂ H V) (σ.comp s : Representation ℂ H W) :=
  Representation.Equiv.mk φ.toLinearEquiv fun g => φ.toIntertwiningMap.isIntertwining' (s g)

end Comp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V]


omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem isSmooth_comp {n : ℕ} {π : Representation ℂ (GL (Fin n) k) V} (h : IsSmooth π) :
    IsSmooth (π.comp (invTranspose n) : Representation ℂ (GL (Fin n) k) V) :=
  fun v => (h v).preimage (continuous_invTranspose n)


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem isIrreducible_comp {n : ℕ} {π : Representation ℂ (GL (Fin n) k) V} (h : π.IsIrreducible) :
    Representation.IsIrreducible (π.comp (invTranspose n) : Representation ℂ (GL (Fin n) k) V) :=
  GlobalTheory.CosocleComp.isIrreducible_comp (fun g => ⟨_, invTranspose_invTranspose n g⟩) h

def dual (x : IrrGL (k := k)) : IrrGL (k := k) :=
  IrrGL.of (x.rep.comp (invTranspose x.1)) (isSmooth_comp x.2.rep.smooth) (isIrreducible_comp x.2.rep.irr)


omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem dual_of {n : ℕ} (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible) :
    dual (IrrGL.of π hs hi) = IrrGL.of (π.comp (invTranspose n)) (isSmooth_comp hs) (isIrreducible_comp hi) :=
  IrrGL.of_eq_of.2 ⟨compEquiv (IrrGL.equivOf π hs hi).symm (invTranspose n)⟩


omit [IsNonarchimedeanLocalField k] in
theorem dual_dual (x : IrrGL (k := k)) : dual (dual x) = x := by
  refine (dual_of _ _ _).trans (Eq.trans (IrrGL.of_eq_of.2 ⟨?_⟩) (IrrGL.of_rep x))
  refine Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun g => ?_
  ext v
  show x.rep (invTranspose x.1 (invTranspose x.1 g)) v = x.rep g v
  rw [invTranspose_invTranspose]

end GlobalTheory.DualityMap
