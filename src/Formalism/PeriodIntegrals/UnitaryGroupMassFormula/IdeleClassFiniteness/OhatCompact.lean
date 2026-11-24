module

public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
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

namespace PIW.ClassFinD

open NumberField IsDedekindDomain

def Ohat (F : Type) [Field F] [NumberField F] : Subring (FiniteAdeleRing (𝓞 F) F) where
  carrier := {a | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F}
  mul_mem' := fun {a b} ha hb v => by have h := mul_mem (ha v) (hb v); exact h
  one_mem' := fun v => (v.adicCompletionIntegers F).one_mem
  add_mem' := fun {a b} ha hb v => by have h := add_mem (ha v) (hb v); exact h
  zero_mem' := fun v => (v.adicCompletionIntegers F).zero_mem
  neg_mem' := fun {a} ha v => by have h := neg_mem (ha v); exact h

def MatInt {F : Type} [Field F] [NumberField F] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Prop :=
  ∀ i j, M i j ∈ Ohat F

theorem matInt_one (F : Type) [Field F] [NumberField F] (n : ℕ) :
    MatInt (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · exact (Ohat F).one_mem
  · exact (Ohat F).zero_mem

theorem matInt_mul {F : Type} [Field F] [NumberField F] {n : ℕ}
    {M N : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)} (hM : MatInt M) (hN : MatInt N) :
    MatInt (M * N) := by
  intro i j
  rw [Matrix.mul_apply]
  exact (Ohat F).sum_mem fun k _ => (Ohat F).mul_mem (hM i k) (hN k j)

def KGL (F : Type) [Field F] [NumberField F] (n : ℕ) :
    Subgroup (GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) where
  carrier := {g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F) | MatInt g.val ∧ MatInt g⁻¹.val}
  one_mem' := by
    refine ⟨?_, ?_⟩
    · exact matInt_one F n
    · rw [inv_one]; exact matInt_one F n
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]; exact matInt_mul ha hb
    · rw [mul_inv_rev, Units.val_mul]; exact matInt_mul hb' ha'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨ha', by rw [inv_inv]; exact ha⟩

abbrev glIncl (F : Type) [Field F] [NumberField F] (n : ℕ) :
    GL (Fin n) F →* GL (Fin n) (FiniteAdeleRing (𝓞 F) F) :=
  Units.map (RingHom.mapMatrix (algebraMap F (FiniteAdeleRing (𝓞 F) F))).toMonoidHom

def BorelKGL : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ),
    ∃ T : Finset (GL (Fin n) (FiniteAdeleRing (𝓞 F) F)),
      ∀ x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F), ∃ γ : GL (Fin n) F, ∃ s ∈ T, ∃ k ∈ KGL F n,
        x = glIncl F n γ * s * k

end PIW.ClassFinD

end
