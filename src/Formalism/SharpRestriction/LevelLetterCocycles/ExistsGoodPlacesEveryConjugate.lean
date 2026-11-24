module

public import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.MainNotions.N.TwAll

section Conj

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem psiAt_side_zpow {Γ A : Type} [Group Γ] [CommGroup A] (b b' : Bool) (ψ : Γ →* A) (a : ℤ) :
    ∃ a' : ℤ, a'.natAbs = a.natAbs ∧ Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b' (ψ ^ a) = Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (ψ ^ a') := by
  cases b <;> cases b'
  · exact ⟨a, rfl, rfl⟩
  · refine ⟨-a, Int.natAbs_neg a, ?_⟩
    simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, zpow_neg]
  · refine ⟨-a, Int.natAbs_neg a, ?_⟩
    simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, zpow_neg]
  · exact ⟨a, rfl, rfl⟩

end Conj

end Formalism.MainNotions.N.TwAll

namespace Formalism.MainNotions

open Formalism.MainNotions.N.TwAll

def TwGoodAll (D : D7) (I : TwIn D) (i : D.ntw.Tw) (b : Bool) (Q : Finset (PlE D.host)) (k' : ℕ)
    (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ) : Prop :=
  ∀ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l i) → TwGoodOne D I i b Q k' (ψ ^ a)

def rawPack {D : D7} (C : NChoice D) (w : D.what₂.places.Pl) : TwPack D := ⟨C.twI w, C.Q w, C.k' w, C.psi' w⟩

def IntegralHeckeEveryConjugate (D : D7) (bkP : BlochKatoReduction.BK D) (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.pin bkP) i → ∀ eps' : ℝ, 0 < eps' →
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, IntegralHeckeForms.FullRk D.nexp E i j b (IntegralHeckeForms.SgJ D.nexp E i j b)) →
    ∀ S : ∀ (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b),
      (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, IntegralHeckeForms.BasisOf D.nexp i j b (IntegralHeckeForms.SgJ D.nexp E i j b) (S j b)) →
    ∀ A : Finset (PlE D.host),
    ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ),
      ∀ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l i) →
        IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.pin bkP) E N0 i eps' S A Q k' (ψ' ^ a)

end Formalism.MainNotions

namespace Formalism.MainNotions.N.KillingConditions

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal

section Kill

variable {D : D7} (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))

end Kill

end Formalism.MainNotions.N.KillingConditions

namespace Formalism.MainNotions.N.KillingConditions

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal

section C6

variable {D : D7} (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))

end C6

end Formalism.MainNotions.N.KillingConditions

namespace Formalism.MainNotions.LatticeVariant

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open Formalism.MainNotions.IntegralHeckeForms (HkIdx hkO TwOK T3 IsLatIn sIdx specU)
open Formalism.MainNotions.BlochKatoReduction.Gen (psiAt nval SetHyp PsiOk partA partAT partC partD)
open scoped TensorProduct

section All

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} {Y : NExp D.R D.host D.what₂ D.LL0 N X}



end All

end Formalism.MainNotions.LatticeVariant

namespace Formalism.MainNotions.IntegralHeckeForms

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

section All

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} {Y : NExp D.R D.host D.what₂ D.LL0 N X}


variable (Y) in
def goodTwistExistsAllCoprimePowers (bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X) (E : ExpDat Y) (N0 : X.Tw → ℕ) (i : X.Tw) : Prop :=
  Formalism.MainNotions.BlochKatoReduction.Gen.SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' →
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, FullRk Y E i j b (SgJ Y E i j b)) →
  ∀ S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b),
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, BasisOf Y i j b (SgJ Y E i j b) (S j b)) →
  ∀ A : Finset (PlE D.host),
  ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ),
    ∀ a : ℤ, a.natAbs.Coprime (X.l i) → GoodTw Y bkP E N0 i eps' S A Q k' (ψ' ^ a)

end All

end Formalism.MainNotions.IntegralHeckeForms

namespace Formalism.MainNotions

end Formalism.MainNotions

namespace Formalism.MainNotions.N.TwAll

open Formalism.MainNotions.BlochKatoReduction.Gen (nval)

section Tame

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}

end Tame

end Formalism.MainNotions.N.TwAll

namespace Formalism.MainNotions.N.KillingConditions

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Formalism.MainNotions.N.TwAll

section DensityAveraging

variable {D : D7}

end DensityAveraging

end Formalism.MainNotions.N.KillingConditions

end
