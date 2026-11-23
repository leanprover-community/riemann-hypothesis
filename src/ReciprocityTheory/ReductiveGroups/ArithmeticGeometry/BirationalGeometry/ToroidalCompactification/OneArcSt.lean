module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi

def PullCubCompSt : Prop :=
  ∀ (S S' S'' : Scheme.{0}) (G : Over S) (G' : Over S') (G'' : Over S'') [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G''] (m : CubeMap G' G) (m' : CubeMap G'' G') (n : CubeMap G'' G)
    (L : RigLB G) (L' : RigLB G') (L'' : RigLB G'') (c : CubicalStr G L) (c' : CubicalStr G' L')
    (c'' : CubicalStr G'' L''), n.F = m'.F ≫ m.F → n.F3 = m'.F3 ≫ m.F3 → n.e = m'.e ≫ m.e →
    m.IsPullCubical c' c → m'.IsPullCubical c'' c' → n.IsPullCubical c'' c

def PullCubCancelSt : Prop :=
  ∀ (S S' S'' : Scheme.{0}) (G : Over S) (G' : Over S') (G'' : Over S'') [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G''] (m : CubeMap G' G) (m' : CubeMap G'' G') (n : CubeMap G'' G)
    (L : RigLB G) (L' : RigLB G') (L'' : RigLB G'') (c : CubicalStr G L) (c' : CubicalStr G' L')
    (c'' : CubicalStr G'' L''), n.F = m'.F ≫ m.F → n.F3 = m'.F3 ≫ m.F3 → n.e = m'.e ≫ m.e →
    m.IsPullCubical c' c → n.IsPullCubical c'' c → m'.IsPullCubical c'' c'

def SABCompSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' S'' : Scheme.{0}) (t : SAB H S)
    (t' : SAB H S') (t'' : SAB H S'') (f : S' ⟶ S) (g : S'' ⟶ S') (m : SABMap t' t f) (m' : SABMap t'' t' g),
    ∃ n : SABMap t'' t (g ≫ f), n.φ = m'.φ ≫ m.φ

def SABCancelSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' S'' : Scheme.{0}) (t : SAB H S)
    (t' : SAB H S') (t'' : SAB H S'') (f : S' ⟶ S) (g : S'' ⟶ S') (m : SABMap t' t f) (n : SABMap t'' t (g ≫ f)),
    ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ

def AbLocusOneSt : Prop :=
  ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (K : Type) [Field K] (t : Sp K ⟶ S),
    IsProper (pullback.snd G.hom t) → Set.range t ⊆ abLocus G

def ProjProperSt : Prop :=
  ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R), IsProjOver f → IsProper f

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
