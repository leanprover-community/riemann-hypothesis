module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished
public import Mathlib.RingTheory.PowerSeries.Exp
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

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

def RhoUniqueStatement : Prop :=
  ∀ (O S : Type) [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O] [CommRing S] [Algebra O S]
    (P : Polynomial O), P.IsDistinguishedAt (maximalIdeal O) →
    ∀ ρ ρ' : PowerSeries O →ₐ[O] PowerSeries S, ρ X = ρ' X →
    constantCoeff (Polynomial.aeval (ρ X) P) = 0 → ρ = ρ'

def RhoComplStatement : Prop :=
  ∀ (O LL S : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Field LL] [Algebra O LL] [IsFractionRing O LL] [CommRing S] [Algebra LL S] [Algebra O S] [IsScalarTower O LL S]
    (P : Polynomial O), P.IsDistinguishedAt (maximalIdeal O) → ∀ ρ : PowerSeries O →ₐ[O] PowerSeries S,
    (∃ w : (PowerSeries S)ˣ, ρ (P : PowerSeries O) = (w : PowerSeries S) * X) →
    (∀ r : Polynomial LL, Polynomial.aeval (constantCoeff (ρ X)) r = 0 → P.map (algebraMap O LL) ∣ r) →
    ∀ (k : ℕ) (a : PowerSeries O), (X : PowerSeries S) ^ k ∣ ρ a → (P : PowerSeries O) ^ k ∣ a

def RhoUnitStatement : Prop :=
  ∀ (O S : Type) [CommRing O] [CommRing S] [Algebra O S] (ρ : PowerSeries O →ₐ[O] PowerSeries S)
    (p a : PowerSeries O) (c : O), constantCoeff (ρ p) = 0 → IsUnit (algebraMap O S c) →
    C c ∈ Ideal.span {p, a} → IsUnit (ρ a)

def PsCoprimeStatement : Prop :=
  ∀ (O : Type) [CommRing O] (l : ℕ) (φ : PowerSeries O →ₐ[O] PowerSeries O),
    (X * (X + C (l : O)) : PowerSeries O) ∣ φ X →
    (∀ s : ℕ, (C (l : O) : PowerSeries O) ∈ Ideal.span {(⇑φ)^[s] (X + C (l : O)), X}) ∧
    ∀ s s' : ℕ, s ≠ s' →
      (C (l : O) : PowerSeries O) ∈ Ideal.span {(⇑φ)^[s] (X + C (l : O)), (⇑φ)^[s'] (X + C (l : O))}

def CycloDistStatement : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (l s : ℕ), l.Prime → (l : O) ∈ maximalIdeal O →
    ((Polynomial.cyclotomic (l ^ (s + 1)) O).comp (Polynomial.X + 1)).IsDistinguishedAt (maximalIdeal O)

def CycloSimpleStatement : Prop :=
  ∀ (LL S : Type) [Field LL] [CharZero LL] [CommRing S] [Algebra LL S] (m : ℕ), 0 < m → ∀ (ζ : S) (E : PowerSeries S),
    Polynomial.aeval ζ (Polynomial.cyclotomic m LL) = 0 → constantCoeff E = 1 → derivative E = E →
    ∃ w : (PowerSeries S)ˣ, Polynomial.aeval (C ζ * E) (Polynomial.cyclotomic m LL) = (w : PowerSeries S) * X

def ExpRescaleStatement : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra ℚ S] (E : PowerSeries S), constantCoeff E = 1 → derivative E = E →
    E = PowerSeries.exp S ∧ ∀ a : ℕ, E ^ a = rescale (a : S) E

def DescendDvdStatement : Prop :=
  ∀ (O : Type) [CommRing O] (ι : PowerSeries O →ₐ[O] PowerSeries O) (m : ℕ), 0 < m →
    (∃ w : (PowerSeries O)ˣ, ι X = (w : PowerSeries O) * X ^ m) →
    Function.Injective ι ∧ ∀ p a : PowerSeries O, ι p ∣ ι a → p ∣ a

def PiSeriesStatement : Prop :=
  ∀ (LL ι : Type) [Field LL],
    (∀ f : ι → PowerSeries LL, ∃! F : PowerSeries (ι → LL), ∀ i, PowerSeries.map (Pi.evalRingHom (fun _ => LL) i) F = f i) ∧
    ∀ F : PowerSeries (ι → LL),
      (∀ k : ℕ, (X : PowerSeries (ι → LL)) ^ k ∣ F ↔
        ∀ i, (X : PowerSeries LL) ^ k ∣ PowerSeries.map (Pi.evalRingHom (fun _ => LL) i) F) ∧
      (IsUnit F ↔ ∀ i, IsUnit (PowerSeries.map (Pi.evalRingHom (fun _ => LL) i) F))

def SplitComplStatement : Prop :=
  ∀ (O LL : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Field LL] [CharZero LL] [Algebra O LL] [IsFractionRing O LL] (l s : ℕ), l.Prime → (l : O) ∈ maximalIdeal O →
    (∃ ζ₀ : LL, IsPrimitiveRoot ζ₀ (l ^ (s + 1))) → ∀ ρ : LL → (PowerSeries O →ₐ[O] PowerSeries LL),
    (∀ ζ, IsPrimitiveRoot ζ (l ^ (s + 1)) → 1 + ρ ζ X = C ζ * PowerSeries.exp LL) →
    ∀ (k : ℕ) (a : PowerSeries O), (∀ ζ, IsPrimitiveRoot ζ (l ^ (s + 1)) → (X : PowerSeries LL) ^ k ∣ ρ ζ a) →
    (((Polynomial.cyclotomic (l ^ (s + 1)) O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) ^ k ∣ a

end LevelStatements.Lv
