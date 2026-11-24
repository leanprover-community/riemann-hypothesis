module

public import Formalism.DistinguishedUnitIdeals.AprimeCuts
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.CutPlace
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.AprimeArith
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.ExponentWindows

theorem exists_cuts_exponent_bounds : AprimeCuts := by
  obtain ⟨C, hC, hA⟩ := Formalism.TruncatedSeriesCounting.WachCoordinates.exists_constant_exponent_inequalities
  refine ⟨C, hC, ?_⟩
  intro ℓ hℓ n j _ size b w S η rr hj hjn _hsize hCb hsep hrr

  obtain ⟨cuts, ell, hne, hcuts⟩ :=
    exists_cuts_of_sparse_thick n j (fun a => b ≤ size a ∧ size a ≤ b + η) hj hjn hsep
  refine ⟨cuts, ell, hne, fun c hc => ?_⟩
  obtain ⟨h1, h2, h3, _h4, h5, h6, _h7, h8, _h9⟩ := hcuts c hc
  refine ⟨h1, h2, h3, h5, h6, h8, ?_, ?_⟩
  · intro k _ hk
    exact (hA ℓ hℓ b w S η j (3 * j + 1) _ _ rr hj hCb le_rfl hk.1 hk.2 hk.1 hk.2 hrr).1
  · intro k k' _ _ hk hk'
    obtain ⟨_, _, e1, e2, e3⟩ :=
      hA ℓ hℓ b w S η j (3 * j + 1) _ _ rr hj hCb le_rfl hk'.1 hk'.2 hk.1 hk.2 hrr
    exact ⟨e1, e2, e3⟩

end Formalism.ExponentWindows
