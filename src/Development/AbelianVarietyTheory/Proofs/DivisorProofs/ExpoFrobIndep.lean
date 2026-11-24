module

public import Formalism.PieriBlockIdeals.LatticeInclusionRealSettingAlt
public import Formalism.PieriBlockIdeals.PieriColumnMinors.WeightBounds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

namespace GlobalTheory

theorem expo_frob_indep : ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P →
    ∀ (fr : ℕ → ι → ι) (cj : ℕ → ι → Bool), ({ W with fr := fr, cj := cj } : Wts ι).Ok P ∧
      ∀ l : ℕ, l.Prime → W.WRange P l → ({ W with fr := fr, cj := cj } : Wts ι).coarseWeightBound P l = W.coarseWeightBound P l := by
  intro P hH hL ι _ _ W hW fr cj
  have hW' : ({ W with fr := fr, cj := cj } : Wts ι).Ok P :=
    { anti := hW.anti, what₂ := hW.what₂, block := hW.block, centre := hW.centre, window := hW.window,
      cloud := hW.cloud, low := hW.low, thick := hW.thick, other := hW.other }
  refine ⟨hW', ?_⟩
  intro l hl hR
  have hN := (places_real_holds P hH hL ι W hW (fun _ => 0)).2
  have hN' := (places_real_holds P hH hL ι ({ W with fr := fr, cj := cj } : Wts ι) hW' (fun _ => 0)).2
  have hi : ({ W with fr := fr, cj := cj } : Wts ι).iW P l = W.iW P l := by
    funext τ
    unfold Wts.iW SizeData₂.depth
    obtain ⟨a1, a2⟩ := hN l hl hR.1 hR.2.2.1 τ
    obtain ⟨b1, b2⟩ := hN' l hl hR.1 hR.2.2.1 τ
    rw [a1, a2, b1, b2]
    rfl
  unfold Wts.coarseWeightBound
  rw [hi]
  rfl

end GlobalTheory
