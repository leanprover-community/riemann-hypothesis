module

public import Formalism.SatakeDualWeyl.Statement
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
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

open TensorProduct

namespace Formalism.RankGapBounds.FormsTensorLocalization

open Formalism.UG

def LatIncl {k : Type} [CommRing k] {A : Type} [AddCommGroup A] [Module k A]
    (l : k) (B : Submodule k A) (e : ℕ) : Prop :=
  ∀ x : A, l ^ e • x ∈ B

def tensSub {k : Type} [CommRing k] {ι : Type} {A : ι → Type} [∀ i, AddCommGroup (A i)]
    [∀ i, Module k (A i)] (B : ∀ i, Submodule k (A i)) : Submodule k (⨂[k] i, A i) :=
  LinearMap.range (PiTensorProduct.map fun i => (B i).subtype)

def formsIn {G : Type} [Group G] {k : Type} [CommRing k] {W : Type} [AddCommGroup W]
    [Module k W] (Γ K : Subgroup G) (ρK : Representation k K W) (U : Submodule k W) :
    Submodule k (G → W) :=
  AMFK k Γ K ρK ⊓ Submodule.pi Set.univ (fun _ => U)

def locSet {T : Type} [CommRing T] {M : Type} [AddCommGroup M] [Module T M]
    (S : Submonoid T) (N : Set M) : Set (LocalizedModule S M) :=
  {y | ∃ x ∈ N, ∃ s : S, LocalizedModule.mk x s = y}

def TensorStep : Prop :=
  ∀ (k : Type) [CommRing k] (ι : Type) [Fintype ι] (A : ι → Type) [∀ i, AddCommGroup (A i)]
    [∀ i, Module k (A i)] (B : ∀ i, Submodule k (A i)) (l : k) (e : ι → ℕ),
    (∀ i, LatIncl l (B i) (e i)) → ∀ y : ⨂[k] i, A i, l ^ (∑ i, e i) • y ∈ tensSub B

end Formalism.RankGapBounds.FormsTensorLocalization
