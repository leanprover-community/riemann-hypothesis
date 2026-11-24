module

public import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapTheorem
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
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.WachLatticeTwists.RamifiedBlockRings.Statement

@[expose] public section

noncomputable section

open Formalism.RepresentationBoundsCohomology.ringDataObjects (AbsIrr BlockDiagonalIrreducibleAt)
open Formalism.RepresentationBoundsCohomology.FIN (IsCycG)

namespace Formalism.AdicCompletionExports

section Mat

variable {k k' : Type*} [Field k] [Field k'] (σ : k ≃+* k')

end Mat

theorem isCycG_cycZ (l : ℕ) [Fact l.Prime] (Ek Ω O : Type) [Field Ek] [NumberField Ek] [Field Ω] [Algebra Ek Ω]
    [IsAlgClosure Ek Ω] [CommRing O] (f : ℤ_[l] →+* O) :
    IsCycG l ((Units.map f.toMonoidHom).comp (ReciprocityTheory.Gal.cycZ (F := Ek) (Ω := Ω) l)) := by
  intro g n ζ hζ
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed Ek
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap Ek Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hspec := cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (Ω ≃ₐ[Ek] Ω) Ω g) ζ hζ
  set x : ℤ_[l] := ((ReciprocityTheory.Gal.cycZ (F := Ek) (Ω := Ω) l g : ℤ_[l]ˣ) : ℤ_[l]) with hx
  refine ⟨(PadicInt.toZModPow n x).val, hspec, ?_⟩
  have h2 : x - (((PadicInt.toZModPow n x).val : ℕ) : ℤ_[l]) ∈ Ideal.span {(l : ℤ_[l]) ^ n} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [Ideal.mem_span_singleton] at h2 ⊢
  obtain ⟨y, hy⟩ := h2
  refine ⟨f y, ?_⟩
  have h3 := congrArg f hy
  rw [map_sub, map_natCast, map_mul, map_pow, map_natCast] at h3
  exact h3

end Formalism.AdicCompletionExports
