module

public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
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

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.TwAll

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X) (bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X)

def admissibleIndexBoundAllPowers (N0 : X.Tw → ℕ) : Prop :=
  ∀ i : X.Tw, X.NonzeroIndexPlace i → Formalism.MainNotions.BlochKatoReduction.Gen.SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' → ∀ F : RFam Y i,
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, ABHyp Y i F j b) →
    ∀ A0 : Finset (PlE D.host),
    ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ), ∀ a : ℤ, IsCoprime a (X.l i : ℤ) →
      Formalism.MainNotions.BlochKatoReduction.Gen.PsiOk i A0 Q k' (ψ' ^ a) ∧ Formalism.MainNotions.BlochKatoReduction.Gen.partAT bkP i Q k' (ψ' ^ a) eps' ∧
      Formalism.MainNotions.BlochKatoReduction.Gen.partC N0 i Q k' (ψ' ^ a) eps' ∧ Formalism.MainNotions.BlochKatoReduction.Gen.partD i Q k' (ψ' ^ a) eps' ∧
      partAB Y i F Q k' (ψ' ^ a) eps'

def goodTwistExistsAllCoprimePowers (E : ExpDat Y) (N0 : X.Tw → ℕ) (i : X.Tw) : Prop :=
  Formalism.MainNotions.BlochKatoReduction.Gen.SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' →
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, FullRk Y E i j b (SgJ Y E i j b)) →
  ∀ S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b),
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, BasisOf Y i j b (SgJ Y E i j b) (S j b)) →
  ∀ A : Finset (PlE D.host),
  ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ), ∀ a : ℤ, IsCoprime a (X.l i : ℤ) →
    GoodTw Y bkP E N0 i eps' S A Q k' (ψ' ^ a)

variable {Y} (T : NTh D.R D.host D.what₂ D.LL0 N X Y)

def TypeKept (E : ExpDat Y) : Prop := ∀ i, X.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k Q
  (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ), TwOK i k Q ψ → UnrG ψ → ∀ a ∈ E.Dat0 i j b,
    Y.thPsi i j b k Q ψ a ⊆ ((((Fm0 Y i j b).restrictScalars (X.O i)).baseChange (X.Ok i k) :
      Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b)) : Set (X.Ok i k ⊗[X.O i] Y.Fm i j b))

end GlobalTheory.TwAll
