module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
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

open Formalism.MainNotions.G Formalism.FrobeniusOrbits NumberField

namespace Formalism.BasicNotions

structure GatTies (D : D7) where

  gat_k : ∀ u w h, (D.gat u w h).P.m + 1 = D.R.k

  gat_n : ∀ u w h (v : Fin (D.gat u w h).P.nV) (P : Ideal (𝓞 D.host.E)) [P.IsPrime]
    [P.LiesOver (Ideal.span {((D.what₂.places.resChar w : ℕ) : ℤ)})] (σ : D.host.E ≃ₐ[ℚ] D.host.E), IsArithFrobAt ℤ σ P →
    (D.gat u w h).P.n' v = orderOf (D.host.galE σ).2

  gat_pos : ∀ u w h, (Σ v : Fin (D.gat u w h).P.nV, Fin ((D.gat u w h).P.n' v)) ≃ D.what₂.Tau

  gat_step : ∀ u w h (v : Fin (D.gat u w h).P.nV) (s : Fin ((D.gat u w h).P.n' v))
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {((D.what₂.places.resChar w : ℕ) : ℤ)})]
    (σ : D.host.E ≃ₐ[ℚ] D.host.E), IsArithFrobAt ℤ σ P →
    ((D.eTau (gat_pos u w h ⟨v, posAdd s 1⟩) : D.R.Psi) : D.R.GG) =
      ((D.eTau (gat_pos u w h ⟨v, s⟩) : D.R.Psi) : D.R.GG) *
        D.host.galE σ * D.R.cc

  gat_lam : ∀ u w h (v : Fin (D.gat u w h).P.nV) (s : Fin ((D.gat u w h).P.n' v))
    (i : Fin ((D.gat u w h).P.m + 1)),
    (D.gat u w h).P.lam0 v s i =
      ((D.fm u).lam 0 (gat_pos u w h ⟨v, s⟩)).w
        ⟨i.1, by have h1 := gat_k u w h; have h2 := i.2; simp only [Ranks.N]; omega⟩

end Formalism.BasicNotions
