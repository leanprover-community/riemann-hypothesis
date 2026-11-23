module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MemRamLine
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.ExtRep
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

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.cupRaw :
    ∀ {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [Field k] (Φ : Fr O Γ) (a : O →+* k) (l : ℕ) [Fact l.Prime] [CharP k l], (Set.range a).Finite → Φ.Ok a → ∀ 𝒩 : Set Γ → Prop, Φ.Gys l 𝒩 → ∀ (w w' : ℤ × ℤ) (J : Type) [Finite J] (y : J → Γ → k), (∀ j, Φ.Coc a w' (y j)) →
      ∃ N', 𝒩 N' ∧ ∃ (x : Γ → k) (m : Φ.ι → k), (Φ.wN N').Coc a w x ∧ Φ.LocTriv a w x m ∧ (∃ g, a (Φ.rt w g) = 1 ∧ x g ≠ 0) ∧
        ∀ j, ∃ z, (Φ.wN N').Cup a w w' x (y j) z m := by
  intro O Γ k _ _ _ _ _ _ Φ a l _ _ hfin hok 𝒩 hG w w' J _ y hy
  obtain ⟨M, i1, i2, i3, i4, i5, ρ, p, q, m0, hc, hN, hp, hq, hm0, hpm⟩ :=
    Gys.extRep Φ a l hfin hok.lc w w' J y hy
  obtain ⟨N', hN', c, hcZ, hc0, hloc, g, hg1, hcg, hspan⟩ :=
    hG M ρ hc (fun g hg => hN g (hok.kill g hg) (fun j => (hy j).kill g hg)) m0 hm0
  obtain ⟨hcont, hcoc⟩ := (mem_Z1_iff_cocycle ρ c).1 hcZ
  have hlc : IsLocallyConstant c := (IsLocallyConstant.iff_continuous c).2 hcont
  have hrt : ∀ u, (Φ.wN N').rt u = Φ.rt u := fun u => rfl
  choose mm hmm using hloc
  have hpg : p (c g) ≠ 0 := hpm _ hspan hcg
  refine ⟨N', hN', fun s => p (c s), fun v => -p (mm v), ?_, ?_, ?_, ?_⟩
  · refine ⟨hlc.comp p, ?_, ?_⟩
    · intro s t
      rw [hrt, hcoc, map_add (f := _), hp]
    · intro s hs
      simp [hc0 s hs]
  · intro v s hs
    show p (c s) = -p (mm v) - a ↑((Φ.rt w) s) * -p (mm v)
    rw [hmm v s hs, map_sub, hp]
    ring
  · refine ⟨g, ?_, hpg⟩
    have h := hp g (c g)
    rw [hg1] at h
    change p (c g) = _ at h
    have h2 : (a ↑((Φ.rt w) g) - 1) * p (c g) = 0 := by linear_combination -h
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact sub_eq_zero.1 h3
    · exact absurd h3 hpg
  · intro j
    refine ⟨fun s => q j (c s), hlc.comp (q j), ?_, ?_, ?_⟩
    · intro s t
      simp only [hrt]
      rw [hcoc, map_add (f := _), hq]
      ring
    · intro s hs
      simp [hc0 s hs]
    · intro v
      refine ⟨-q j (mm v), fun s hs => ?_⟩
      simp only [hrt]
      rw [hmm v s hs, map_sub, hq]
      ring
