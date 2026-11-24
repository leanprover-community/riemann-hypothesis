module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.RingTheory.AlgebraicIndependent.Basic

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

open GlobalTheory.CompanionTheory.Ar.FlagBun

def IsGenFam (Ω G : Type) [Field Ω] [Field G] [Algebra Ω G] {S : Type} {r : S → ℕ}
    (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G) : Prop :=
  (∀ s a, u s a a = 1) ∧ (∀ s a b, a < b → u s a b = 0) ∧
    AlgebraicIndependent Ω (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) ∧
    IntermediateField.adjoin Ω (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2) = ⊤

def revInv {G : Type} [Field G] {r : ℕ} (u : Matrix (Fin r) (Fin r) G) : Matrix (Fin r) (Fin r) G :=
  (u.transpose⁻¹).submatrix Fin.rev Fin.rev

theorem genU_isGenFam (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) : IsGenFam Ω (GenField Ω r) (genU Ω r) := by
  have hdiag : ∀ s (a : Fin (r s)), genU Ω r s a a = 1 := fun s a => by
    simp [genU]
  have habove : ∀ s (a b : Fin (r s)), a < b → genU Ω r s a b = 0 := fun s a b h => by
    simp [genU, not_lt.2 h.le, h.ne]
  have hbelow : ∀ q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1},
      genU Ω r q.1 q.2.1.1 q.2.1.2 =
        algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X (R := Ω) (σ := GenIx r) q) :=
    fun q => by
      simp only [genU]
      exact dif_pos q.2.2
  refine ⟨hdiag, habove, ?_, ?_⟩
  · have hinj : Function.Injective
        (IsScalarTower.toAlgHom Ω (MvPolynomial (GenIx r) Ω) (GenField Ω r)) := by
      rw [IsScalarTower.coe_toAlgHom']
      exact IsFractionRing.injective _ _
    have hX := (MvPolynomial.algebraicIndependent_X (GenIx r) Ω).map' hinj
    have hfun : (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} =>
        genU Ω r q.1 q.2.1.1 q.2.1.2) =
        (IsScalarTower.toAlgHom Ω (MvPolynomial (GenIx r) Ω) (GenField Ω r)) ∘ MvPolynomial.X := by
      funext q
      exact hbelow q
    rw [hfun]
    exact hX
  · rw [eq_top_iff]
    intro x _
    have hXmem : ∀ q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1},
        algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X (R := Ω) (σ := GenIx r) q) ∈
          IntermediateField.adjoin Ω
            (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => genU Ω r q.1 q.2.1 q.2.2) := by
      intro q
      rw [← hbelow q]
      exact IntermediateField.subset_adjoin _ _ ⟨⟨q.1, q.2.1⟩, rfl⟩
    have hA : ∀ a : MvPolynomial (GenIx r) Ω,
        algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) a ∈
          IntermediateField.adjoin Ω
            (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => genU Ω r q.1 q.2.1 q.2.2) := by
      intro a
      induction a using MvPolynomial.induction_on
      · rename_i c
        rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
        exact IntermediateField.algebraMap_mem _ c
      · rename_i p q hp hq
        rw [map_add (f := _)]
        exact add_mem hp hq
      · rename_i p i hp
        rw [map_mul]
        exact mul_mem hp (hXmem i)
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (GenIx r) Ω) x
    exact div_mem (hA a) (hA b)

end GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl
