module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinrankAdjoinVarsField
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section


theorem _root_.GlobalTheory.T.finrank_adjoin_vars_field :
    ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (fn : Ω₀ →+* Ω) (I : Type) (d : ℕ),
      0 < d →
      (letI : Algebra Ω₀ Ω := fn.toAlgebra
       Module.finrank Ω₀ Ω = d) →
      letI : Algebra Ω₀ (FractionRing (MvPolynomial I Ω)) :=
        ((algebraMap Ω (FractionRing (MvPolynomial I Ω))).comp fn).toAlgebra
      Module.finrank (IntermediateField.adjoin Ω₀ (Set.range fun q : I =>
        algebraMap (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω)) (MvPolynomial.X q)))
        (FractionRing (MvPolynomial I Ω)) = d := by
  intro Ω₀ Ω _ _ fn I d hd hfin
  let : Algebra Ω₀ Ω := fn.toAlgebra
  have : FiniteDimensional Ω₀ Ω := Module.finite_of_finrank_pos (hfin ▸ hd)
  let : Algebra Ω₀ (FractionRing (MvPolynomial I Ω)) :=
    ((algebraMap Ω (FractionRing (MvPolynomial I Ω))).comp fn).toAlgebra
  have hdegree :=
    GlobalTheory.CompanionTheory.FieldDeg.finrank_fraction_over_adjoin_X_eq Ω₀ Ω I rfl
  exact hdegree.trans hfin
