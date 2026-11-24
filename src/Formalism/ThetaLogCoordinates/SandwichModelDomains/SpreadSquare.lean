module

public import Formalism.ThetaLogCoordinates.SandwichModelDomains.StatementW
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.WeightCompApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.DivStable

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.InvariantFactorPaths.INST

open Formalism.GradedWeylDivisibility Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.InvariantFactorPaths.PW

def Spread (R : Type) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) (l : ℕ) : Prop :=
  ∀ f ∈ dualWeyl R r n ν, ∀ g ∈ dualWeyl R r n ν, ∀ m ∈ f.support, ∀ m' ∈ g.support, ∀ a : Fin r,
    rowDeg m a ≤ rowDeg m' a + l

def SpreadTop : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (r n : ℕ) (ν : Fin n → ℕ) (l : ℕ), (∀ t, ν t ≤ l) → Spread R r n ν l

def SpreadSquare : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (ν : Fin n → ℕ) (l : ℕ), (∀ s t, ν s ≤ ν t + l) → Spread R n n ν l

def vecL {n : ℕ} (ν : Fin n → ℕ) : Letters n := ⟨fun _ => true, ν⟩

def swp (R : Type) [CommRing R] (r n : ℕ) :
    MvPolynomial (Fin r × Fin n) R ≃ₐ[R] MvPolynomial (Fin n × Fin r) R :=
  renameEquiv R (Equiv.prodComm (Fin r) (Fin n))

def GR (p : ℕ) [Fact p.Prime] (r : ℕ) {n : ℕ} (ν : Fin n → ℕ) :
    GlW ℚ_[p] (MvPolynomial (Fin n × Fin r) ℚ_[p]) r :=
  GAe p (vecL ν) n (OrderIso.refl (Fin r)).toOrderEmbedding

def RowGlOne : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (r n : ℕ) (ν : Fin n → ℕ) (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) ℚ_[p]),
    swp ℚ_[p] r n (rowDiv ℚ_[p] a b 1 f) = (GR p r ν).E a b (swp ℚ_[p] r n f)

def RowGlDiv : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (r n : ℕ) (ν : Fin n → ℕ) (a b : Fin r), a ≠ b →
    ∀ (k : ℕ) (f : MvPolynomial (Fin r × Fin n) ℚ_[p]),
      swp ℚ_[p] r n (rowDiv ℚ_[p] a b k f) =
        ((k.factorial : ℚ_[p]))⁻¹ • (((GR p r ν).E a b) ^ k) (swp ℚ_[p] r n f)

def SwpWt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (r n : ℕ) (ν : Fin n → ℕ) (μ : Fin r → ℤ) (f : MvPolynomial (Fin r × Fin n) ℚ_[p]),
    (GR p r ν).IsWt μ (swp ℚ_[p] r n f) ↔ ∀ m ∈ f.support, ∀ a, (rowDeg m a : ℤ) = μ a

def SwpPol : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (r n : ℕ) (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) ℚ_[p]),
    IsWeightedHomogeneous (colW r n) f ν → swp ℚ_[p] r n f ∈ Pol p r (vecL ν)

def SwpInt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (r n : ℕ) (f : MvPolynomial (Fin r × Fin n) ℚ_[p]),
    swp ℚ_[p] r n f ∈ IntPol p (Fin n × Fin r) ↔
      ∃ f0 : MvPolynomial (Fin r × Fin n) ℤ_[p], map (algebraMap ℤ_[p] ℚ_[p]) f0 = f

def CoreQp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ l : ℕ, Spread ℚ_[p] r n ν l →
    ∀ x ∈ dualWeyl ℤ_[p] r n ν, ((p : ℤ_[p]) ^ sExp p r l) • x ∈ weyl ℤ_[p] r n hn ν

def DescentZ : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ e : ℕ,
    (∀ x ∈ dualWeyl ℤ_[p] r n ν, ((p : ℤ_[p]) ^ e) • x ∈ weyl ℤ_[p] r n hn ν) →
    ∀ f ∈ dualWeyl ℤ r n ν, ∃ c : ℤ, ¬ (p : ℤ) ∣ c ∧ (c * (p : ℤ) ^ e) • f ∈ weyl ℤ r n hn ν

def AscentDomain : Prop :=
  ∀ (p : ℕ) (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (e : ℕ),
    (∀ f ∈ dualWeyl ℤ r n ν, ∃ c : ℤ, ¬ (p : ℤ) ∣ c ∧ (c * (p : ℤ) ^ e) • f ∈ weyl ℤ r n hn ν) →
    ∀ (O : Type) [CommRing O] [IsDomain O], PrimeToPUnits p O →
      ∀ x ∈ dualWeyl O r n ν, ((p : O) ^ e) • x ∈ weyl O r n hn ν

end Formalism.InvariantFactorPaths.INST
