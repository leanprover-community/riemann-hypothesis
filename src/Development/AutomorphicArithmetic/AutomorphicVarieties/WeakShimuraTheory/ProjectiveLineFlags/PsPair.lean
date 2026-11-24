module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp

namespace UpperTheory.V.Ws

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}

structure Tower.PsPair (T : Tower D) {c' : Coef l} (h : c.O ≤ c'.O) (k : Type) [Field k] [Algebra c'.O k]
    (Q : PD T.ι (G T.F Ω) (PowerSeries k)) : Prop where
  loc : ∀ a ∈ maximalIdeal c'.O, algebraMap c'.O k a = 0
  pair : (T.fr ∅).IsPair ((algebraMap c'.O (PowerSeries k)).comp (inc h)) Q
  cont : Q.Cont (maximalIdeal (PowerSeries k))
  cp : ∀ g, (Q.r g).charpoly.map (PowerSeries.constantCoeff : PowerSeries k →+* k) =
    ∏ i, (X - C (algebraMap c'.O k (inc h (chi D T.pr i (resQ T.F g)))))
  psi : ∀ v i, ∀ s ∈ Dec (F := T.F) (T.pl v),
    PowerSeries.constantCoeff (Q.ψ v i s) = algebraMap c'.O k (inc h (chi D T.pr i (resQ T.F s)))

namespace Link

variable {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) {R : Type} [CommRing R] [Algebra c'.O R]

def IsRho (ρ : K.V.frame.G₀ →* GL (Fin 4) R) (Q : PD T.ι (G T.F Ω) R) : Prop :=
  ∀ g : G T.L Ω, W.mat ρ (K.V.pr g) = algebraMap c'.O R (K.κ g) • Q.r (resLe T.F_le g)

def IsPsi (ψ : ∀ v : K.V.frame.Vl, Fin 4 → K.V.frame.Gv v →* Rˣ) (Q : PD T.ι (G T.F Ω) R) : Prop :=
  ∀ (v : W.Vl l T.L) (i : Fin 4) (g : Dec (F := T.L) (K.s.A v)),
    ((ψ v i g : Rˣ) : R) = algebraMap c'.O R (K.κ g) * Q.ψ (K.e v) i (resLe T.F_le g)

end Link

end UpperTheory.V.Ws

end
