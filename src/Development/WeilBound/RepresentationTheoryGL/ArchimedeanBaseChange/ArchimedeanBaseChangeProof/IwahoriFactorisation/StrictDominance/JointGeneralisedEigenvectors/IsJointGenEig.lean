module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.TwistedIndependenceLemma.TwistedIndependence
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

open GlobalTheory.PRep

namespace PositivityTheory.SphericalProduct

structure CassData (G : Type) [Group G] [TopologicalSpace G] where

  N : Subgroup G

  Nm : Subgroup G

  T : Subgroup G

  J : Subgroup G
  isOpen_J : IsOpen (J : Set G)
  isCompact_J : IsCompact (J : Set G)
  isClosed_N : IsClosed (N : Set G)
  isClosed_Nm : IsClosed (Nm : Set G)
  isClosed_alt : IsClosed (T : Set G)
  norm_N : ∀ t ∈ T, t ∈ Subgroup.normalizer (N : Set G)
  norm_Nm : ∀ t ∈ T, t ∈ Subgroup.normalizer (Nm : Set G)

  fact_low : ∀ x ∈ J, ∃ a ∈ J ⊓ Nm, ∃ b ∈ J ⊓ T, ∃ c ∈ J ⊓ N, x = a * b * c

  fact_up : ∀ x ∈ J, ∃ c ∈ J ⊓ N, ∃ b ∈ J ⊓ T, ∃ a ∈ J ⊓ Nm, x = c * b * a

variable {G : Type} [Group G] [TopologicalSpace G]

namespace CassData

def JT (D : CassData G) : Subgroup D.T := D.J.comap D.T.subtype

def IsDom (D : CassData G) (t : D.T) : Prop :=
  (∀ n ∈ D.J ⊓ D.N, (t : G) * n * (t : G)⁻¹ ∈ D.J ⊓ D.N) ∧
  (∀ n ∈ D.J ⊓ D.Nm, (t : G)⁻¹ * n * (t : G) ∈ D.J ⊓ D.Nm) ∧
  (∀ x ∈ D.J ⊓ D.T, (t : G) * x * (t : G)⁻¹ ∈ D.J ⊓ D.T ∧ (t : G)⁻¹ * x * (t : G) ∈ D.J ⊓ D.T)

def IsStrDom (D : CassData G) (t : D.T) : Prop :=
  D.IsDom t ∧ (∀ n ∈ D.N, ∃ j : ℕ, (t : G) ^ j * n * ((t : G) ^ j)⁻¹ ∈ D.J ⊓ D.N) ∧
    ∀ U : Set G, IsOpen U → (1 : G) ∈ U → ∃ j : ℕ, ∀ n ∈ D.J ⊓ D.Nm, ((t : G) ^ j)⁻¹ * n * (t : G) ^ j ∈ U

def piN (D : CassData G) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) :
    Representation ℂ D.T (Jacquet π D.N) :=
  jacquet π D.N D.T.subtype (fun m => D.norm_N m m.2)

abbrev proj (D : CassData G) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (v : V) :
    Jacquet π D.N :=
  Submodule.Quotient.mk v

end CassData

open CassData

variable (G) [IsTopologicalGroup G]

def A1 : Prop :=
  ∀ (D : CassData G) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π →
    ∀ t t' : D.T, D.IsDom t → D.IsDom t' → ∀ U U' : Module.End ℂ (fixed π D.J),
      PositivityTheory.Lbc.IsHeckeOpG π D.J (t : G) U → PositivityTheory.Lbc.IsHeckeOpG π D.J (t' : G) U' →
      PositivityTheory.Lbc.IsHeckeOpG π D.J ((t : G) * t') (U * U')

def A2 : Prop :=
  ∀ (D : CassData G) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π →
    ∀ t : D.T, D.IsDom t → ∀ U : Module.End ℂ (fixed π D.J), PositivityTheory.Lbc.IsHeckeOpG π D.J (t : G) U →
      ∀ v : fixed π D.J, D.proj π ((U v : fixed π D.J) : V) = D.piN π t (D.proj π (v : V))

def A4 : Prop :=
  ∀ (D : CassData G) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsAdmissible π →
    (∃ t : D.T, D.IsStrDom t) →
    (∀ v : fixed π D.J, D.proj π (v : V) ∈ fixed (D.piN π) D.JT) ∧
    ∀ w ∈ fixed (D.piN π) D.JT, ∃ v : fixed π D.J, D.proj π (v : V) = w

end PositivityTheory.SphericalProduct

end
