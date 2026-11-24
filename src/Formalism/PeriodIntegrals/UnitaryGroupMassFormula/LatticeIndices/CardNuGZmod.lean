module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LeviEmbeddingBlock32
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Block31OfBlocks
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst

@[expose] public section

noncomputable section

namespace MassDataIdxStIm

open Matrix
open Formalism.DoubleCosetMeasures (IsUpUni upUniG)
open Formalism.FourierDecayAlt.S3 Formalism.L2.SG.TypedSets

variable {A : Type} [CommRing A] {r k : ℕ}

def parGEquiv {P : Matrix (Fin k) (Fin k) A → Prop} (hP : GP P) :
    parG (r := r) hP ≃ {x : Matrix (Idx r k) (Idx r k) A // Par P x} where
  toFun g := ⟨(g : GL (Idx r k) A), g.2⟩
  invFun x := ⟨Matrix.GeneralLinearGroup.mk'' x.1 (par_det hP x.2), x.2⟩
  left_inv g := by ext; rfl
  right_inv x := rfl

abbrev nuG (A : Type) [CommRing A] (r k : ℕ) : Subgroup (GL (Idx r k) A) := parG (r := r) (gpUni (A := A) (k := k))

abbrev sG (A : Type) [CommRing A] (r k : ℕ) : Subgroup (GL (Idx r k) A) := parG (r := r) (gpUnit (A := A) (k := k))

theorem card_nuG (K : Type) [Field K] [Fintype K] (r k : ℕ) :
    Nat.card (nuG K r k) = Nat.card {x : Matrix (Idx r k) (Idx r k) K // IsN x} * Nat.card (upUniG K k) := by
  have hdet : ∀ u : Matrix (Fin k) (Fin k) K, IsUpUni u → IsUnit u.det := by
    intro u hu
    rw [Matrix.det_of_upperTriangular hu.1]
    simp [hu.2]
  have hU : Nat.card (upUniG K k) = Nat.card {u : Matrix (Fin k) (Fin k) K // IsUpUni u} :=
    Nat.card_congr
      { toFun := fun g => ⟨(g : GL (Fin k) K), g.2⟩
        invFun := fun u => ⟨Matrix.GeneralLinearGroup.mk'' u.1 (hdet u.1 u.2), u.2⟩
        left_inv := fun g => by ext; rfl
        right_inv := fun u => rfl }
  have hN : ∀ x : Matrix (Idx r k) (Idx r k) K,
      IsN x ↔ Par (fun h : Matrix (Fin k) (Fin k) K => h = 1) x := by
    intro x
    unfold IsN Par
    constructor
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩
      exact ⟨h1, h2, h4, h5, h6, 1, rfl, by rw [h3, midEmb_one]⟩
    · rintro ⟨h1, h2, h4, h5, h6, h, rfl, h3⟩
      exact ⟨h1, h2, by rw [h3, midEmb_one], h4, h5, h6⟩
  have hcN : Nat.card {x : Matrix (Idx r k) (Idx r k) K // IsN x} =
      Fintype.card K ^ (r * (r - 1) + 2 * r * (k + 1) + r ^ 2) := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight hN), card_par]
    simp
  calc Nat.card (nuG K r k)
      = Nat.card {x : Matrix (Idx r k) (Idx r k) K // Par IsUpUni x} :=
        Nat.card_congr (parGEquiv (r := r) (gpUni (A := K) (k := k)))
    _ = _ := by rw [card_par, hcN, hU, mul_comm]

theorem card_sG (K : Type) [Field K] [Fintype K] (r k : ℕ) :
    Nat.card (sG K r k) = Nat.card (GL (Fin k) K) * Nat.card {x : Matrix (Idx r k) (Idx r k) K // IsN x} := by
  have hG : Nat.card (GL (Fin k) K) = Nat.card {h : Matrix (Fin k) (Fin k) K // IsUnit h.det} :=
    Nat.card_congr
      { toFun := fun g => ⟨(g : Matrix (Fin k) (Fin k) K),
          (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit g)⟩
        invFun := fun h => Matrix.GeneralLinearGroup.mk'' h.1 h.2
        left_inv := fun g => by ext; rfl
        right_inv := fun h => rfl }
  have hN : ∀ x : Matrix (Idx r k) (Idx r k) K,
      IsN x ↔ Par (fun h : Matrix (Fin k) (Fin k) K => h = 1) x := by
    intro x
    unfold IsN Par
    constructor
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩
      exact ⟨h1, h2, h4, h5, h6, 1, rfl, by rw [h3, midEmb_one]⟩
    · rintro ⟨h1, h2, h4, h5, h6, h, rfl, h3⟩
      exact ⟨h1, h2, by rw [h3, midEmb_one], h4, h5, h6⟩
  have hcN : Nat.card {x : Matrix (Idx r k) (Idx r k) K // IsN x} =
      Fintype.card K ^ (r * (r - 1) + 2 * r * (k + 1) + r ^ 2) := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight hN), card_par]
    simp
  calc Nat.card (sG K r k)
      = Nat.card {x : Matrix (Idx r k) (Idx r k) K // Par (fun h => IsUnit h.det) x} :=
        Nat.card_congr (parGEquiv (r := r) (gpUnit (A := K) (k := k)))
    _ = _ := by rw [card_par, hcN, hG]

end MassDataIdxStIm
