module

public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import GroundTheory.AutomorphicForms.GLnLocal
public import GroundTheory.AutomorphicForms.MacdonaldHecke
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

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.BlockD

namespace SatakeBound

open IsDedekindDomain NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GLnLocal Iwasawa
  Finset Matrix
open scoped ValuativeRel

attribute [local instance] GroundTheory.Automorphic.Spherical.fintypeResidue

variable {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

theorem valued_uniformizer_eq :
    Valued.v (uniformizer (w.adicCompletion K) : w.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
  have hS : (Valuation.integer (ValuativeRel.valuation (w.adicCompletion K))) =
      (w.adicCompletionIntegers K).toSubring := by
    ext x
    exact GroundTheory.Global.mem_valuationInteger_iff w x
  let e := RingEquiv.subringCongr hS
  have hirr : Irreducible (e (uniformizer (w.adicCompletion K))) :=
    (MulEquiv.irreducible_iff e).2 (irreducible_uniformizer _)
  have := GroundTheory.Global.valued_of_irreducible (v := w) (K := K)
    (ϖ := ⟨(e (uniformizer (w.adicCompletion K)) : w.adicCompletion K), (e _).2⟩) (by exact hirr)
  simpa [e] using this

theorem valued_le_one_of_mem {x : w.adicCompletion K} (hx : x ∈ 𝒪[w.adicCompletion K]) :
    Valued.v x ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K w).1
    ((GroundTheory.Global.mem_valuationInteger_iff w x).1 hx)

variable {w}

end SatakeBound

end GroundTheory.BlockD
