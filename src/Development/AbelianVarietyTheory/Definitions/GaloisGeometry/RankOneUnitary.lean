module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeSplitOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
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

namespace GlobalTheory.RowTie

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

structure WDTie where

  e : ∀ w : PlE H, A.LP w ≃ WD (E := H.E) (A := N.plOm.1 w) (w := w) (N.plOm.2 w)
  dim : ∀ w (a : A.LP w), (e w a).lpDim = A.lpDim a
  zero : ∀ w, e w (A.lpZero w) = WD.lpZero (N.plOm.2 w)
  sum : ∀ w (a b : A.LP w), e w (A.lpSum a b) = (e w a).lpSum (e w b)
  tw : ∀ w (a : A.LP w) (s : ℝ), e w (A.lpTw a s) = (e w a).lpTw s
  char : ∀ w (a χ : A.LP w), A.lpDim χ = 1 → e w (A.lpChar a χ) = (e w a).lpChar (e w χ)
  mono0 : ∀ w (a : A.LP w), A.mono0 a ↔ (e w a).mono0
  unr : ∀ w (a : A.LP w), A.unr a ↔ (e w a).unr
  frobEig : ∀ w (a : A.LP w), A.unr a → A.frobEig a = (e w a).frobEig
  tempered : ∀ w (a : A.LP w), A.tempered a ↔ (e w a).tempered
  inePol : ∀ w (a : A.LP w), ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol a σ = (e w a).inePol σ

def WDTie.eig {N : NData R H what₂} {A : NAut N} (T : WDTie N A) (w : PlE H) (a : A.LP w) (σ : G H.E N.Om) :
    Multiset ℂ := ((T.e w a).inePol σ).roots

def CharLaws : Prop := ∀ (w : PlE H) (a b χ χ' : A.LP w) (s : ℝ), A.lpDim χ = 1 → A.lpDim χ' = 1 →
  A.lpChar (A.lpSum a b) χ = A.lpSum (A.lpChar a χ) (A.lpChar b χ) ∧
  A.lpChar (A.lpTw a s) χ = A.lpTw (A.lpChar a χ) s ∧
  A.lpChar a (A.lpTw χ s) = A.lpTw (A.lpChar a χ) s ∧
  A.lpChar (A.lpChar a χ) χ' = A.lpChar a (A.lpChar χ χ') ∧
  A.lpChar a (A.lpUnr w {1}) = a

def Cancel : Prop := ∀ (w : PlE H) (a b c : A.LP w), A.lpSum a c = A.lpSum b c → a = b

def PairLift (i : N.Loc) : Prop := ∀ σ P, Pairs N A i σ P → ∀ w, IsSplitPl H w →
  A.locV i P w = liftPar N A i w (A.locW i σ w)

def BCEx (i : N.Loc) : Prop := ∀ P : A.AV i, ∃ Pa, IsBCV N A i P Pa

def ChebSplit : Prop := ∀ S : Finset (PlE H), Dense {σ : G H.E N.Om | ∃ w : PlE H, w ∉ S ∧ IsSplitPl H w ∧
  ∃ B : ValuationSubring N.Om, IsPlaceOver (F := H.E) B w ∧ IsFrob (F := H.E) B (normV w) σ}

def SplitBC (i : N.Loc) : Prop := ∀ P P' : A.AV i,
  (∀ᶠ w in Filter.cofinite, IsSplitPl H w → A.locV i P w = A.locV i P' w) →
  ∀ Pa Pa', IsBCV N A i P Pa → IsBCV N A i P' Pa' → Pa.Perm Pa'

def RepOfLoc (i : N.Loc) : Prop := ∀ P P' : A.AV i,
  (∀ w, IsSplitPl H w → A.locV i P w = A.locV i P' w) →
  (∀ w, ¬ IsSplitPl H w → ubc R.nV (A.satV i P w) = ubc R.nV (A.satV i P' w)) → P = P'

def twSum (L : List ((Σ a : ℕ, A.CG a) × ℝ)) (w : PlE H) : A.LP w :=
  L.foldr (fun p acc => A.lpSum (A.lpTw (A.locG p.1.2 w) p.2) acc) (A.lpZero w)

def IsobaricRigid : Prop := ∀ L L' : List ((Σ a : ℕ, A.CG a) × ℝ), (∀ p ∈ L, 1 ≤ p.1.1) → (∀ p ∈ L', 1 ≤ p.1.1) →
  (∀ᶠ w in Filter.cofinite, twSum N A L w = twSum N A L' w) → L.Perm L'

def RankOneUnitary {N : NData R H what₂} {A : NAut N} (T : WDTie N A) : Prop :=
  ∀ (π : A.CG 1) (w : PlE H) (σ : G H.E N.Om), IsFrob (F := H.E) (N.plOm.1 w) (normV w) σ →
    ∀ α ∈ T.eig w (A.locG π w) σ, ‖α‖ = 1

def IotaRed (D : D7) : Prop := ∀ i : D.nd.Loc,
  haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
  ∃ (B : ValuationSubring ℂ) (κ : IsLocalRing.ResidueField B ≃+* Formalism.CyclotomicNorms.Fbar (D.what₂.places.resChar (D.nd.w i))),
    (∀ y : D.nd.O i, ∃ h : iotaO D.nd D.naut i y ∈ B,
      fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
        (κ (IsLocalRing.residue B ⟨_, h⟩)) = D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) y)) ∧
    ∀ k v x, ∃ h : D.ntypes.teichC k x ∈ B, D.ntypes.iota k v (D.nd.w i) x = κ (IsLocalRing.residue B ⟨_, h⟩)

end GlobalTheory.RowTie
