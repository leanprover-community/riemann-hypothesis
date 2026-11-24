module

public import ReciprocityTheory.GroupCohomology.TransgressionStatement
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx

universe u

theorem lowNat_holds : LowNatStatement.{u} := by
  intro R _ G _ _ _ G' _ _ _ M M' P e₀ e₁ e₂ e₀' e₁' e₂' hL hL'
  refine ⟨?_, ?_, ?_⟩
  · intro x
    obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    apply Subtype.ext
    have hw : M'.coch.d 0 (P.hom.Z 0 ⟨c, hc⟩).1 = 0 := (P.hom.Z 0 ⟨c, hc⟩).2
    have hc' : M.coch.d 0 c = 0 := hc
    change (e₀' (M'.coch.cls 0 (P.hom.Z 0 ⟨c, hc⟩).1 hw) : M'.V) =
      P.u (e₀ (M.coch.cls 0 c hc'))
    have h1 := hL'.1 (P.hom.Z 0 ⟨c, hc⟩).1 hw
    have h2 := hL.1 c hc'
    rw [h1, h2]
    show P.u (c.1 fun i => P.φ (![] i)) = P.u (c.1 ![])
    rw [show (fun i => P.φ (![] i)) = (![] : Fin 0 → G) from funext fun i => i.elim0]
  · intro x
    obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨hz, he⟩ := hL.2.1 c hc
    have hw : M'.coch.d 1 (P.hom.Z 1 ⟨c, hc⟩).1 = 0 := (P.hom.Z 1 ⟨c, hc⟩).2
    obtain ⟨hz', he'⟩ := hL'.2.1 (P.hom.Z 1 ⟨c, hc⟩).1 hw
    change e₁' (M'.coch.cls 1 (P.hom.Z 1 ⟨c, hc⟩).1 hw) =
      P.h1 (e₁ (M.coch.cls 1 c hc))
    rw [he', he]
    unfold Pair.h1 pairH1DecompositionMap
    rw [Submodule.mapQ_apply]
    congr 1
    apply Subtype.ext
    funext g
    show P.u (c.1 fun i => P.φ (![g] i)) = P.u (c.1 ![P.φ g])
    rw [show (fun i => P.φ (![g] i)) = ![P.φ g] from by funext i; fin_cases i; rfl]
  · intro x
    obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨hz, he⟩ := hL.2.2 c hc
    have hw : M'.coch.d 2 (P.hom.Z 2 ⟨c, hc⟩).1 = 0 := (P.hom.Z 2 ⟨c, hc⟩).2
    obtain ⟨hz', he'⟩ := hL'.2.2 (P.hom.Z 2 ⟨c, hc⟩).1 hw
    change e₂' (M'.coch.cls 2 (P.hom.Z 2 ⟨c, hc⟩).1 hw) =
      P.h2 (e₂ (M.coch.cls 2 c hc))
    rw [he', he]
    unfold Pair.h2 compatiblePairH2
    rw [Submodule.mapQ_apply]
    congr 1
    apply Subtype.ext
    funext g
    show P.u (c.1 fun i => P.φ (![g.1, g.2] i)) = P.u (c.1 ![P.φ g.1, P.φ g.2])
    rw [show (fun i => P.φ (![g.1, g.2] i)) = ![P.φ g.1, P.φ g.2] from by
      funext i; fin_cases i <;> rfl]

end ReciprocityTheory.Coh
