module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions TensorProduct

section Ext

variable {G : Type} [Group G] {LL : Type} [Field LL] {V W : Type} [AddCommGroup V] [Module LL V]
  [AddCommGroup W] [Module LL W]

def IsExt (ρ : Representation LL G V) (ρ' : Representation LL G W) (i : V →ₗ[LL] W) (p : W →ₗ[LL] LL) : Prop :=
  Function.Injective i ∧ Function.Exact i p ∧ Function.Surjective p ∧
    (∀ g x, i (ρ g x) = ρ' g (i x)) ∧ ∀ g y, p (ρ' g y) = p y

def IsCocycleOf (ρ' : Representation LL G W) (i : V →ₗ[LL] W) (p : W →ₗ[LL] LL) (c : G → V) : Prop :=
  ∃ e : W, p e = 1 ∧ ∀ g, ρ' g e = e + i (c g)

variable [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

def extRep (ρ : Representation LL G V) (c : ↥(continuousCocycles ρ)) : Representation LL G (V × LL) where
  toFun g := ((ρ g).coprod (LinearMap.toSpanSingleton LL V ((c : G → V) g))).prod (LinearMap.snd LL V LL)
  map_one' := by
    have h : (c : G → V) 1 = 0 := by simpa using c.2.2 1 1
    refine LinearMap.ext fun x => ?_
    simp [h]
  map_mul' g k := by
    refine LinearMap.ext fun x => ?_
    simp [c.2.2 g k]
    abel

theorem extRep_isExt (ρ : Representation LL G V) (c : ↥(continuousCocycles ρ)) :
    IsExt ρ (extRep ρ c) (LinearMap.inl LL V LL) (LinearMap.snd LL V LL) ∧
      IsCocycleOf (extRep ρ c) (LinearMap.inl LL V LL) (LinearMap.snd LL V LL) (c : G → V) := by
  refine ⟨⟨LinearMap.inl_injective, Function.Exact.inl_snd, LinearMap.snd_surjective, fun g x => ?_,
    fun _ _ => rfl⟩, (0, 1), rfl, fun g => ?_⟩
  · simp [extRep]
  · simp [extRep]

end Ext

section Per

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]

def H1fSubmodule {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] (ρ : Representation LL G V) :
    Submodule LL (H1V ρ) :=
  ((finiteCocycles PD ρ).comap (continuousCocycles ρ).subtype).map (Submodule.mkQ _)

theorem mk_mem_H1fSub {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] (ρ : Representation LL G V)
    (c : ↥(continuousCocycles ρ)) : (Submodule.Quotient.mk c : H1V ρ) ∈ H1fSubmodule PD ρ ↔ (c : G → V) ∈ finiteCocycles PD ρ := by
  refine ⟨?_, fun h => ⟨c, h, rfl⟩⟩
  rintro ⟨c', ⟨-, x, hx⟩, h⟩
  obtain ⟨b, hb⟩ := (Submodule.Quotient.eq _).mp h
  refine ⟨c.2, x - b ⊗ₜ[Qp] (1 : B), fun g => ?_⟩
  have h1 : ρ g b - b = (c' : G → V) g - (c : G → V) g := congrFun hb g
  have h2 : (c : G → V) g = (c' : G → V) g - (ρ g b - b) := by rw [h1]; abel
  have h3 : actVB PD ρ g (b ⊗ₜ[Qp] (1 : B)) = ρ g b ⊗ₜ[Qp] (1 : B) := by simp [actVB]
  have h4 : (c' : G → V) g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x := hx g
  rw [h2, sub_tmul, sub_tmul, h4, map_sub, h3]
  abel

def ExtCrysAt [TopologicalSpace LL] {n : ℕ} (emb : ZMod n → (K₀ →ₐ[Qp] LL)) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [FiniteDimensional LL V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] [IsModuleTopology LL V]
    (ρ : Representation LL G V), (∀ x, Continuous fun g => ρ g x) → IsCrys PD ρ →
  ∀ (W : Type) [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W]
    (ρ' : Representation LL G W) (i : V →ₗ[LL] W) (p : W →ₗ[LL] LL), IsExt ρ ρ' i p →
  ∀ c : ↥(continuousCocycles ρ), IsCocycleOf ρ' i p (c : G → V) →
    (IsCrys PD ρ' ↔ (Submodule.Quotient.mk c : H1V ρ) ∈ H1fSubmodule PD ρ) ∧
    (IsCrys PD ρ' → ∀ (j : ZMod n) (U : Multiset ℤ),
      AdmLoc.HasJumps PD ρ (emb j) U → AdmLoc.HasJumps PD ρ' (emb j) (U + {0}))

end Per

def ExtCrys {l : ℕ} [Fact l.Prime] (P : LocPrime l) : Prop :=
  ∀ (K LL : Loc.FinExt l) (n : ℕ) (emb : ZMod n → (↥(Loc.K0 K) →ₐ[ℚ_[l]] ↥LL.1)) (lam : ↥(Loc.OL LL)),
    AdmLoc.Standing P K LL emb lam → ExtCrysAt (P.PD K) emb

end GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions
