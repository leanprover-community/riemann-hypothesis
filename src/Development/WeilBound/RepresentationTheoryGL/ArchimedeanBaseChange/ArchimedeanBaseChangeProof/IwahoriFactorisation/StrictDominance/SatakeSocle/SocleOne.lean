module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.GenericPrincipalSeries.GenericPrincipalSeries
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

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.SphericalProduct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def msOne {n : ℕ} (ξ : Fin n → kˣ →* ℂˣ) (hξ : ∀ i, IsUnram (ξ i)) : Multiset (Segment k) :=
  Finset.univ.val.map fun i =>
    Segment.single (IrrGL.ofChar (ξ i) (isSmoothChar_of_isUnram (hξ i))) (IrrGL.isCusp_ofChar _ _)


variable (k) in
def atUnif {n : ℕ} (ξ : Fin n → kˣ →* ℂˣ) : Fin n → ℂˣ := fun i => ξ i (Zls.unifU k)

def AbsAnti {n : ℕ} (α : Fin n → ℂˣ) : Prop := Antitone fun i => ‖((α i : ℂˣ) : ℂ)‖

def SocleOne : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (n : ℕ) (ξ : Fin n → kˣ →* ℂˣ) (hξ : ∀ i, IsUnram (ξ i)), AbsAnti (atUnif k ξ) →
    ∀ hd : ∑ a, (IrrGL.ofChar (ξ a) (isSmoothChar_of_isUnram (hξ a))).1 = n,
      (∃ x : IrrGL (k := k), x.1 = n ∧ IsL (msOne ξ hξ) x.rep) ∧
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
        IsL (msOne ξ hξ) π → IsSocle π (prodIrr (fun a => IrrGL.ofChar (ξ a) (isSmoothChar_of_isUnram (hξ a))) hd)

def LOneSat : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (n : ℕ) (ξ : Fin n → kˣ →* ℂˣ) (hξ : ∀ i, IsUnram (ξ i))
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π →
      (IsL (msOne ξ hξ) π ↔ HasSatake π (atUnif k ξ))

def ExpSat : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (n : ℕ) (hd : ∑ _a : Fin n, 1 = n) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → IsAdmissible π → π.IsIrreducible →
    ∀ (ξ : Fin n → kˣ →* ℂˣ), (∀ i, IsUnram (ξ i)) → AbsAnti (atUnif k ξ) →
    (∃ v : Jacquet π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)), v ≠ 0 ∧
      ∀ t : Levi k (fun _ : Fin n => Fin 1),
        v ∈ Module.End.maxGenEigenspace (jac (stdBlocks (fun _ : Fin n => 1) hd) π t) (PositivityTheory.Lbc.torusChar ξ t)) →
    HasSatake π (atUnif k ξ)

end PositivityTheory.SphericalProduct

end
