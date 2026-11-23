module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.OrbClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open UpperTheory.V.Cj.A

theorem UpperTheory.V.Cj.A.satClosed :
    SatClosed := by
  intro Γ V S _ _ _ _ d G hP hC l hl T K hT hK hKY s
  have hcont : ∀ s', ContinuousOn (fun p : V => l s' p • p) G.Y := fun s' =>
    (hl.1 s').1.continuousOn.smul continuousOn_id
  have hmem : ∀ s', ∀ p ∈ G.Y, l s' p • p ∈ G.Y := fun s' p hp =>
    hC _ ((hl.1 s').2.1 p hp) p hp
  have horb : ∀ s', IsOpen (G.Y \ {p | ∃ γ : Γ, G.σ γ s = s' ∧ G.ρ γ p ∈ (fun p : V => l s' p • p) '' K}) := fun s' =>
    orbClosed Γ V S d G hP _ (by rintro _ ⟨k, hk, rfl⟩; exact hmem s' k (hKY hk))
      (hK.image_of_continuousOn ((hcont s').mono hKY)) s s'
  have hopen := (hcont s).isOpen_inter_preimage G.isOpen (hT.isOpen_biInter fun s' _ => horb s')
  convert hopen using 1
  ext p
  simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, Set.mem_setOf_eq]
  refine and_congr_right fun hp => ⟨fun h s' hs' => ⟨hmem s p hp, ?_⟩, fun h => ?_⟩
  · rintro ⟨γ, rfl, k, hk, hk'⟩
    have h1 := (hl.1 (G.σ γ s)).2.1 k (hKY hk)
    have h2 := (hl.1 s).2.1 p hp
    refine h ⟨γ, (l (G.σ γ s) k)⁻¹ * l s p, mul_pos (inv_pos.2 h1) h2, hs', ?_⟩
    have h3 : l (G.σ γ s) k • k = l s p • G.ρ γ p := by rw [← map_smul]; exact hk'
    rw [mul_smul, ← h3, inv_smul_smul₀ h1.ne']
    exact hk
  · rintro ⟨γ, t, ht, hs', hk⟩
    refine (h _ hs').2 ⟨γ, rfl, _, hk, ?_⟩
    show l (G.σ γ s) (t • G.ρ γ p) • t • G.ρ γ p = _
    rw [(hl.1 _).2.2 t ht _ (G.maps γ p hp), hl.2 γ s p hp, map_smul, smul_smul]
    congr 1
    field_simp
