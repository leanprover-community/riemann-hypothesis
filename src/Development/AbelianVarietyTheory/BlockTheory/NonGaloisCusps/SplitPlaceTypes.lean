module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

section Host

variable {R : Ranks} (H : Host R)

def SplitRowPrime (l : ℕ) : Prop :=
  l.Prime ∧ 5 ≤ l ∧ l ≠ H.q ∧ l ≠ H.d ∧ (∀ k, l ≠ H.g k) ∧ H.cls l = PrimeClass.splitK

def halfType (s : Bool) : Set (H.E →+* ℂ) :=
  match s with
  | true => H.cmType
  | false => {φ | φ.comp (H.conj : H.E →+* H.E) ∈ H.cmType}

def PlacesSplit (l : ℕ) : Prop :=
  ∀ w ∈ placesOver H.E l,
    w.asIdeal.ramificationIdx ℤ = 1 ∧
    (∃ w' ∈ placesOver H.E l, IsConjPl H w w') ∧
    ∀ w', IsConjPl H w w' → w' ≠ w

end Host

section Loc

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}
  (nbr : Br.NBr N) (i : N.Loc)

def EmbIn (s : Bool) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i))
    (τ : Br.Kw nbr i w hw →ₐ[ℚ_[N.l i]] Br.LL nbr i w hw) : Prop :=
  (∀ x : H.E, ∃ y : what₂.LL, Br.toLLK (nbr i w hw) (N.embK i y) = τ (Br.cEw nbr i w hw x)) ∧
  ∃ φ ∈ halfType H s,
    ∀ (x : H.E) (y : what₂.LL), Br.toLLK (nbr i w hw) (N.embK i y) = τ (Br.cEw nbr i w hw x) →
      what₂.embLL y = φ x

def PlIn (s : Bool) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i)) : Prop :=
  Nonempty (Br.Kw nbr i w hw →ₐ[ℚ_[N.l i]] Br.LL nbr i w hw) ∧ ∀ τ, EmbIn nbr i s w hw τ

def columns (s : Bool) : Set (HeightOneSpectrum (𝓞 H.E)) :=
  {w | ∃ hw : w ∈ placesOver H.E (N.l i), PlIn nbr i s w hw}

def TypesPair : Prop :=
  (∀ (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i)),
    Loc.K0 (nbr i w hw).Kw = (nbr i w hw).Kw.1) ∧
  (∀ (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i)) τ,
    ¬ (EmbIn nbr i true w hw τ ∧ EmbIn nbr i false w hw τ)) ∧
  (∀ (w w' : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i))
      (hw' : w' ∈ placesOver H.E (N.l i)), IsConjPl H w w' →
    (PlIn nbr i true w hw ∧ PlIn nbr i false w' hw') ∨
      (PlIn nbr i false w hw ∧ PlIn nbr i true w' hw')) ∧
  ∀ s : Bool,
    (∀ w ∈ placesOver H.E (N.l i), ∀ w', IsConjPl H w w' →
      Xor (w ∈ columns nbr i s) (w' ∈ columns nbr i s)) ∧
    (columns nbr i s).Finite ∧
    ∀ w ∈ placesOver H.E (N.l i), locDeg H.E w * (columns nbr i s).ncard = R.f

end Loc

def SplitRow_at (D : D7) : Prop :=
  (∀ l : ℕ, SplitRowPrime D.host l → PlacesSplit D.host l) ∧
  ∀ i : D.nd.Loc, SplitRowPrime D.host (D.nd.l i) → TypesPair (N := D.nd) D.nbr i

end GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

end
