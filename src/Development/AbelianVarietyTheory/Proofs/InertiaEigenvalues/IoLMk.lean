module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BKFinLevel

variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

def ioL (L : Lattice (O := O) ρ) (ϖ : O) (r : ℕ) :
    (↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) →ₗ[O] (V ⧸ L.T) :=
  (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T).liftQ
    (L.T.mkQ ∘ₗ (((algebraMap O LL ϖ)⁻¹ ^ r • (LinearMap.id : V →ₗ[LL] V)).restrictScalars O) ∘ₗ
      L.T.subtype) (by
    intro x hx
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨y, -, rfl⟩ := hx
    rw [LinearMap.mem_ker]
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, Submodule.coe_smul,
      LinearMap.coe_restrictScalars, LinearMap.smul_apply, LinearMap.id_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    rw [← algebraMap_smul LL (ϖ ^ r) (y : V), smul_smul, map_pow, ← mul_pow]
    rcases eq_or_ne (algebraMap O LL ϖ) 0 with h | h
    · rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr; simpa using y.2
      · rw [h, inv_zero, zero_mul, zero_pow hr.ne', zero_smul]; exact L.T.zero_mem
    · rw [inv_mul_cancel₀ h, one_pow, one_smul]; exact y.2)

theorem ioL_mk (L : Lattice (O := O) ρ) (ϖ : O) (r : ℕ) (y : ↥L.T) :
    ioL L ϖ r (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ((algebraMap O LL ϖ)⁻¹ ^ r • (y : V)) := rfl

variable {V' : Type} [AddCommGroup V'] [Module LL V'] [Module O V'] [IsScalarTower O LL V']
  {ρ' : Representation LL G V'}

def cupQ (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ') (P : V →ₗ[LL] V' →ₗ[LL] LL) (ϖ : O)
    (r : ℕ) (c : G → ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T))
    (c' : G → ↥L'.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L'.T)) (x : G × G) : LL :=
  (algebraMap O LL ϖ)⁻¹ ^ r * P (Formalism.MainNotions.LocalSituation.liftQ L _ (c x.1)) (ρ' x.1 (Formalism.MainNotions.LocalSituation.liftQ L' _ (c' x.2)))

end GlobalTheory.BKFinLevel
