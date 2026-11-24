module

public import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace Formalism.IndefR.NX.Core

structure RatCore where
  L0 : Type
  [fieldBase : Field L0]
  [numberFieldBase : NumberField L0]
  Ks : Type
  [fKs : Field Ks]
  [nfKs : NumberField Ks]
  [algKs : Algebra Ks L0]

  Tw : Type
  O : Tw → Type
  [crO : ∀ i, CommRing (O i)]
  [domO : ∀ i, IsDomain (O i)]

  fractionRingMaps : ∀ (i : Tw) (_b : Bool), L0 →+* FractionRing (O i)

  G : Type
  [grpG : Group G]
  [finG : Fintype G]
  WL : ℕ → Type
  [acgWL : ∀ j, AddCommGroup (WL j)]
  [modWL : ∀ j, Module L0 (WL j)]
  [modKsWL : ∀ j, Module Ks (WL j)]
  [towWL : ∀ j, IsScalarTower Ks L0 (WL j)]
  [modOLWL : ∀ j, Module (𝓞 L0) (WL j)]
  [towOLWL : ∀ j, IsScalarTower (𝓞 L0) L0 (WL j)]
  [modOKsWL : ∀ j, Module (𝓞 Ks) (WL j)]
  [towOKsWL : ∀ j, IsScalarTower (𝓞 Ks) Ks (WL j)]
  W : ℕ → (L0 →+* ℂ) → Type
  [nW : ∀ j σ, NormedAddCommGroup (W j σ)]
  [ipW : ∀ j σ, InnerProductSpace ℂ (W j σ)]

  A : ∀ j, Arith.FormsL L0 Ks (WL j) (W j) G

attribute [instance] RatCore.fieldBase RatCore.numberFieldBase RatCore.fKs RatCore.nfKs RatCore.algKs RatCore.crO RatCore.domO
  RatCore.grpG RatCore.finG RatCore.acgWL RatCore.modWL RatCore.modKsWL RatCore.towWL RatCore.modOLWL
  RatCore.towOLWL RatCore.modOKsWL RatCore.towOKsWL RatCore.nW RatCore.ipW

variable (C : RatCore)

end Formalism.IndefR.NX.Core
