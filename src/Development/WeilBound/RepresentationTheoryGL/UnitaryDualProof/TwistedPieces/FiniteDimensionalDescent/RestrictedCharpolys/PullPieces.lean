module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.PieceGood
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix Polynomial GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.TP.Desc.Restr

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def Fr (k : Type) (p c : ℕ) : Type := k

instance (p c : ℕ) : AddCommGroup (Fr k p c) := inferInstanceAs (AddCommGroup k)
instance (p c : ℕ) : TopologicalSpace (Fr k p c) := inferInstanceAs (TopologicalSpace k)

def frMod (p c : ℕ) [Fact p.Prime] [CharP k p] : Module k (Fr k p c) :=
  Module.compHom k (iterateFrobenius k p c)

structure PhiData {n N : ℕ} (q : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k))
    (Z' : Subalgebra k (Matrix (Fin N) (Fin N) k)) (φ : Matrix (Fin n) (Fin n) k →+* Matrix (Fin N) (Fin N) k)
    (e : (Fin n → k) ≃+ (Fin N → k)) : Prop where
  inj : Function.Injective φ
  emb : Topology.IsClosedEmbedding φ
  econt : Continuous e
  econt' : Continuous e.symm
  intertw : ∀ x v, e (x *ᵥ v) = φ x *ᵥ e v
  carrier : (Z' : Set (Matrix (Fin N) (Fin N) k)) = φ '' (Z : Set (Matrix (Fin n) (Fin n) k))
  cen : Bz Z' = φ '' Bz Z
  gz : ∀ g' : GL (Fin N) k, g' ∈ Gz Z' ↔ ∃ g ∈ Gz Z, φ g.val = g'.val
  scal : ∀ a : k, φ (algebraMap k _ (a ^ q)) = algebraMap k _ a
  cr : CR Z'
  mu : mu Z' = mu Z
  roots : HasRoots Z' q
  nil : NilBound Z' q

variable (k)

def FinDim : Prop := ∀ (p c : ℕ) [Fact p.Prime] [CharP k p],
  letI := frMod (k := k) p c
  FiniteDimensional k (Fr k p c) ∧ 0 < Module.finrank k (Fr k p c)

def PhiEx : Prop := ∀ (p c : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z →
  n ≤ p ^ c → ∃ (N : ℕ) (Z' : Subalgebra k (Matrix (Fin N) (Fin N) k)) (φ : Matrix (Fin n) (Fin n) k →+* Matrix (Fin N) (Fin N) k)
    (e : (Fin n → k) ≃+ (Fin N → k)), PhiData (p ^ c) Z Z' φ e

def RestrL : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z →
    ∃ (N q : ℕ) (Z' : Subalgebra k (Matrix (Fin N) (Fin N) k)), CR Z' ∧ mu Z' = mu Z ∧ (∃ c : ℕ, q = p ^ c) ∧
      HasRoots Z' q ∧ NilBound Z' q ∧ ∀ χ : k[X], ∃ l : List k[X],
        (∀ χ' ∈ l, ∃ (m : ℕ) (F' : Fin m → Set (Matrix (Fin N) (Fin N) k)), IsPieces Z' χ' F' ∧ ∀ i, Good Z' (F' i)) →
        ∃ (m : ℕ) (F : Fin m → Set (Matrix (Fin n) (Fin n) k)), IsPieces Z χ F ∧ ∀ i, Good Z (F i)

def PullPieces : Prop :=
  ∀ {n N q : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (Z' : Subalgebra k (Matrix (Fin N) (Fin N) k))
    (φ : Matrix (Fin n) (Fin n) k →+* Matrix (Fin N) (Fin N) k) (e : (Fin n → k) ≃+ (Fin N → k)), CR Z →
    PhiData q Z Z' φ e → ∀ χ : k[X], ∃ l : List k[X],
        (∀ χ' ∈ l, ∃ (m : ℕ) (F' : Fin m → Set (Matrix (Fin N) (Fin N) k)), IsPieces Z' χ' F' ∧ ∀ i, Good Z' (F' i)) →
        ∃ (m : ℕ) (F : Fin m → Set (Matrix (Fin n) (Fin n) k)), IsPieces Z χ F ∧ ∀ i, Good Z (F i)

end PositivityTheory.RgUd.TP.Desc.Restr
