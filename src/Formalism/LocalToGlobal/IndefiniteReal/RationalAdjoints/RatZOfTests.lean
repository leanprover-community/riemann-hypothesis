module

public import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Module NumberField
open scoped InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Rat

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Cx.CxData

section Defs

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)

def RowTest : Prop :=
  ∃ (N : ℕ) (ψ : Fin N → Module.Dual ℂ X.EE), (∀ e, (∀ i, ψ i e = 0) → e = 0) ∧
    ∀ t i (x : A.FR t), ψ i (X.Θ t (X.jR t x)) ∈ Set.range Bs.v0.embedding

def LiftTest : Prop :=
  ∀ j, ∃ (N : ℕ) (ψ : Fin N → Module.Dual ℂ (X.W j)), (∀ w, (∀ i, ψ i w = 0) → w = 0) ∧
    ∀ t i (x : A.FL j t), ψ i (X.θ' j t (X.jL j t x)) ∈ Set.range Bs.v0.embedding

def LiftTestB (b : Bool) : Prop :=
  ∀ j, ∃ (N : ℕ) (ψ : Fin N → Module.Dual ℂ (X.W j)), (∀ w, (∀ i, ψ i w = 0) → w = 0) ∧
    (∀ t i (x : A.FL j t), ψ i (X.θ' j t (X.jL j t x)) ∈ Set.range Bs.v0.embedding) ∧
    ∀ i (k : Fin (X.dW b j)), ψ i (X.w0C b j (Pi.single k 1)) ∈ Set.range Bs.v0.embedding

end Defs

def RatZOfTests : Prop :=
  ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) (cv : CrdV A),
    X.KFormR → X.KFormL → X.JIsoR cv → X.JIsoL cv → RowTest X → LiftTest X → X.RatZ

def RatMuOfRowTest : Prop :=
  ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool), RowTest X → X.H2 cr b → X.RATmu cr b

def RatThOfLiftTest : Prop :=
  ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool),
    LiftTestB X b → X.H5 cr b → X.KForm b → X.EWnorm b → 0 < X.nP b → X.RATth cr b

end Formalism.IndefR.Rat
