module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricCharacterIsCMHostValueDatumStatement
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem isToricElt_of_isLamTie : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (Z : LamDat D), Z.Ok →
    IsLamTie X Z → IsToricElt X ∧ ∀ i, X.NonzeroIndexPlace i → ∀ lam : X.abelian₂ i, ∃ s : ℤ, BlochKatoReduction.Gen.SOk X i lam s := by
  intro D N X Z hZ h
  refine ⟨fun i hi => ?_, fun i hi lam => ?_⟩
  · obtain ⟨hS, ι, hι, hl⟩ := h i hi
    refine ⟨ι, hι, fun lam s hs => ?_⟩
    obtain ⟨j, a, s', ⟨-, hs', hv⟩, u, hu, hQ⟩ := hl lam
    obtain rfl : s = s' := by
      have h1 := hs.1
      have h2 := hs'.1
      omega
    have h1 : 1 ≤ s := by exact_mod_cast hs.2.1
    exact ⟨_, inferInstance, phi D.host, Z.kap j a s, cond0 D.host Z.w0, Z.lam0 (X.l i) j a, u,
      GlobalTheory.T.isHostDatum_kap_lam0_of_ok D Z hZ (X.l i) j a s h1 hs.2.2, hS, hv, hu, hQ⟩
  · obtain ⟨-, ι, -, hl⟩ := h i hi
    obtain ⟨j, a, s, ⟨-, hs, -⟩, -⟩ := hl lam
    exact ⟨s, hs⟩

end GlobalTheory.LamTie
