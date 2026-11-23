module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDefs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

def quotPart (S : Type*) [CommRing S] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (V : Ideal (MRingOver S ι)) (c : K → ℤ) : Submodule S (MRingOver S ι ⧸ V) :=
  Submodule.span S ((Ideal.Quotient.mk V) ''
    {p | (∀ k, 0 ≤ c k) ∧ IsMultiHomog p (fun k => (c k).toNat)})

def GeneratedV (S : Type*) [CommRing S] {K : Type*} [Fintype K] [LinearOrder K] {ι : K → Type*}
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (n : K → ℤ) : Prop :=
  ∀ I : Cell K ι 0, ∃ (r : ℕ) (z : Fin r → CechC S ι (MRingOver S ι ⧸ V) 0)
    (u : Fin r → LocalizedModule (cellMon S I.1) (MRingOver S ι ⧸ V)),
    (∀ j, z j ∈ cechZc ι (quotPart S V) n 0) ∧
    (∀ j, u j ∈ locPart ι (quotPart S V) (cellMon S I.1) (-n)) ∧
    ∑ j, u j * z j I = 1

def AmpleV (S : Type*) [CommRing S] {K : Type*} [Fintype K] [LinearOrder K] {ι : K → Type*}
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (N : K → ℤ) : Prop :=
  ∃ q : ℕ, 1 ≤ q ∧ GeneratedV S V (q • N) ∧
    ∀ e : K → ℤ, ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c → Subsingleton (cechHc ι (quotPart S V) (e + (c * q) • N) 1)

def KAmpStatement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (I : IFamily F ι) (V : Ideal (MRingOver F ι)) (d : ℕ)
    (α : K → ℤ) (b a : ℕ),
    IsFieldIntersection I → IsProjVarF V d → NefOnF I V α → 1 ≤ b → 1 ≤ a →
    AmpleV F V (b • α + fun _ => (a : ℤ))

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
