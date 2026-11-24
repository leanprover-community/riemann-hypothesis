module

public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HalfLevelCoefficients

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

structure IsHalf (D : D7) (Mb : Ideal (𝓞 D.host.E)) : Prop where
  fromK : Mb = Ideal.span {a | a ∈ Mb ∧ a ∈ Algebra.adjoin ℤ {w0E D}}
  prod : Mb * Mb.map (bH D) = Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)}
  coprime : Mb ⊔ Mb.map (bH D) = ⊤

theorem three_le_g (D : D7) (k : Fin 2) : 3 ≤ D.host.g k := by
  have := (D.host.g_prime k).two_le
  have := g_ne_two D k
  omega

def levelAt (D : D7) (Mb : Ideal (𝓞 D.host.E)) (h : IsHalf D Mb) : Level (hostOfRecord D) where
  M := D.host.g 0 * D.host.g 1
  three_le := by
    have := three_le_g D 0
    have := three_le_g D 1
    nlinarith
  odd := ((D.host.g_prime 0).odd_of_ne_two (g_ne_two D 0)).mul ((D.host.g_prime 1).odd_of_ne_two (g_ne_two D 1))
  Mb := Mb
  fromK := h.fromK
  prod := h.prod
  coprime := h.coprime
  A := 1
  A_pos := Nat.one_pos


def PrimesOver (D : D7) (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) : Prop :=
  ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal

def halfOf (D : D7) (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) : Ideal (𝓞 D.host.E) :=
  ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

end GlobalTheory.IndefiniteRowSideFullHecke.HalfLevelCoefficients
