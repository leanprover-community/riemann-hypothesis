module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.TopLeCopiesSelf
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.RepEigCompl
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PRep Matrix UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite
open scoped ComplexOrder

private theorem map_smooth {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] {N : Type}
    [AddCommGroup N] [Module k N] [TopologicalSpace G] [IsTopologicalGroup G]
    (ρ : Representation k G V) (σ : Representation k G N) (hσ : IsSmooth σ) (f : N →ₗ[k] V)
    (hf : ∀ g v, f (σ g v) = ρ g (f v)) (n : N) : f n ∈ smoothPart ρ := by
  let T : Subgroup G :=
    { carrier := {g | ρ g (f n) = f n}
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hy, hx]
      one_mem' := by simp
      inv_mem' := by
        intro x hx
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul]; simp }
  refine T.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset ((hσ n).mem_nhds (by simp)) ?_)
  intro g hg
  have hg' : σ g n = n := hg
  show ρ g (f n) = f n
  rw [← hf, hg']

private theorem smoothRep_smooth {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation k G V) : IsSmooth (smoothRep ρ) := by
  intro v
  have h : IsOpen {g : G | ρ g v.1 = v.1} := v.2
  convert h using 3 with g
  exact Subtype.ext_iff

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.repEigSum :
    ∀ {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] {N : Type} [AddCommGroup N] [Module k N] [CharZero k] [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation k G V) (σ : Representation k G N), IsSmooth σ → ∀ (Y : Submodule k V) (K : Subgroup G) (χ : K →* kˣ), IsCompact (K : Set G) → IsOpen {x : K | χ x = 1} → copies ρ Y σ ⊓ eig ρ K χ = ⨆ f : Into ρ Y σ, (eig σ K χ).map f.1 := by
  intro k G V _ _ _ _ N _ _ _ _ _ ρ σ hσ Y K χ hK hχ
  have hE : (⨆ f : Into ρ Y σ, (eig σ K χ).map f.1) ≤ copies ρ Y σ ⊓ eig ρ K χ := by
    refine iSup_le fun f => ?_
    rintro _ ⟨n, hn, rfl⟩
    refine ⟨Submodule.mem_iSup_of_mem f ⟨n, rfl⟩, fun h => ?_⟩
    rw [← f.2.1, hn h, map_smul]
  refine le_antisymm ?_ hE
  have hC := (repEigCompl σ K χ hσ hK hχ).1
  have hD := (repEigCompl (smoothRep ρ) K χ (smoothRep_smooth ρ) hK hχ).1
  have hT : ∀ f : Into ρ Y σ, ∀ n ∈ twKer σ K χ,
      f.1 n ∈ (twKer (smoothRep ρ) K χ).map (smoothPart ρ).subtype := by
    intro f
    refine (Submodule.span_le (p := Submodule.comap f.1 ((twKer (smoothRep ρ) K χ).map (smoothPart ρ).subtype))).2 ?_
    rintro _ ⟨x, n, rfl⟩
    refine ⟨_, Submodule.subset_span ⟨x, ⟨f.1 n, map_smooth ρ σ hσ f.1 f.2.1 n⟩, rfl⟩, ?_⟩
    rw [map_sub, map_sub, map_smul, map_smul, f.2.1]
    rfl
  have hle : copies ρ Y σ ≤ (⨆ f : Into ρ Y σ, (eig σ K χ).map f.1) ⊔
      (twKer (smoothRep ρ) K χ).map (smoothPart ρ).subtype := by
    refine iSup_le fun f => ?_
    rintro _ ⟨n, rfl⟩
    have hn : n ∈ eig σ K χ ⊔ twKer σ K χ := by rw [hC.sup_eq_top]; trivial
    obtain ⟨a, ha, t, ht, rfl⟩ := Submodule.mem_sup.1 hn
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (Submodule.mem_iSup_of_mem f ⟨a, ha, rfl⟩) (hT f t ht)
  rintro v ⟨hv, hv'⟩
  obtain ⟨e, he, _, ⟨t, ht, rfl⟩, rfl⟩ := Submodule.mem_sup.1 (hle hv)
  have ht' : (t : V) ∈ eig ρ K χ := by
    have := Submodule.sub_mem _ hv' (hE he).2
    simpa using this
  have ht'' : t ∈ eig (smoothRep ρ) K χ := fun h => Subtype.ext (ht' h)
  have h0 : t = 0 := (Submodule.disjoint_def.1 hD.disjoint) t ht'' ht
  subst h0
  simpa using he
