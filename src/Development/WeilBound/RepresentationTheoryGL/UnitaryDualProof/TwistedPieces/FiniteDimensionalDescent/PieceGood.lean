module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.TraceForm
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.IsClosedGzS
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

namespace PositivityTheory.RgUd.TP.Desc

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def primIdem (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Set (Matrix (Fin n) (Fin n) k) :=
  {e | e ∈ Z ∧ IsIdempotentElem e ∧ e ≠ 0 ∧ ∀ f ∈ Z, IsIdempotentElem f → f * e = f → f = 0 ∨ f = e}

def cenSub (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Submodule k (Matrix (Fin n) (Fin n) k) :=
  (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))).toSubmodule

def mu (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : ℕ :=
  ∑ᶠ e ∈ primIdem Z, Module.finrank k ((cenSub Z).map (LinearMap.mulLeft k e)) /
    Module.finrank k (Z.toSubmodule.map (LinearMap.mulLeft k e))

def Good (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (F : Set (Matrix (Fin n) (Fin n) k)) : Prop :=
  (∃ c ∈ Z, ∀ x ∈ F, IsNilpotent (x - c)) ∨
    ∃ (N : ℕ) (S : Subalgebra k (Matrix (Fin N) (Fin N) k)), CR S ∧ mu S < mu Z ∧ (Van S → FibVan Z F)

def HasRoots (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (q : ℕ) : Prop := ∀ a : k, ∃ w ∈ Z, w ^ q = algebraMap k _ a

def NilBound (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (q : ℕ) : Prop := ∀ y ∈ Bz Z, IsNilpotent y → y ^ q = 0

variable (k)

def Restr : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z →
    ∃ (N q : ℕ) (Z' : Subalgebra k (Matrix (Fin N) (Fin N) k)), CR Z' ∧ mu Z' = mu Z ∧ (∃ c : ℕ, q = p ^ c) ∧
      HasRoots Z' q ∧ NilBound Z' q ∧ ∀ χ : k[X], ∃ l : List k[X],
        (∀ χ' ∈ l, ∃ (m : ℕ) (F' : Fin m → Set (Matrix (Fin N) (Fin N) k)), IsPieces Z' χ' F' ∧ ∀ i, Good Z' (F' i)) →
        ∃ (m : ℕ) (F : Fin m → Set (Matrix (Fin n) (Fin n) k)), IsPieces Z χ F ∧ ∀ i, Good Z (F i)

def PieceGood : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] [CharP k p], PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k) →
    ∀ (N q : ℕ) (Z : Subalgebra k (Matrix (Fin N) (Fin N) k)), CR Z → (∃ c : ℕ, q = p ^ c) → HasRoots Z q →
      NilBound Z q → ∀ χ : k[X], ∃ (m : ℕ) (F : Fin m → Set (Matrix (Fin N) (Fin N) k)), IsPieces Z χ F ∧ ∀ i, Good Z (F i)

end PositivityTheory.RgUd.TP.Desc
