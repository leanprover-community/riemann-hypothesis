module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ObstructionBoundFromDuality
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.OdKill
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.InV

@[expose] public section

open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

theorem UpperTheory.V.Pa.B2.odLam :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (X : Type) [CommRing X] [Algebra x.A X] (X'' : Type) [CommRing X''] [Algebra x.A X''] (D D'' : Dat x.A (plOf G)) (_ : IsOd h x X D) (_ : IsOd h x X'' D'') (g : D.Hom D''), Function.Surjective g.f → (∀ u, UrAx l (L.Ju u)) → ∀ w, ∀ y'' ∈ D''.abelian₂ w, ∃ y ∈ D.abelian₂ w, ∀ s, g.fq w (y s) = y'' s := by
  intro l _ L G G0 h n x X _ _ X'' _ _ D D'' o o'' g hg hur w y'' hy
  have hs : ∀ w, Function.Surjective (g.fq w) := by
    intro w q
    obtain ⟨m, rfl⟩ := D''.surj w q
    obtain ⟨m, rfl⟩ := hg m
    exact ⟨D.π w m, g.comm w m⟩
  have top : ∀ w, (∀ s, s ∈ (plOf G).J w) → ∀ y'' ∈ D''.abelian₂ w, ∃ y ∈ D.abelian₂ w, ∀ s, g.fq w (y s) = y'' s := by
    rintro w hw y'' ⟨-, Y, hY⟩
    obtain ⟨Y, rfl⟩ := hs _ Y
    refine ⟨d0 (D.Q w).ρ Y, ⟨coboundaries_le_cocycles _ (D.Q w).cont ⟨Y, rfl⟩, Y, fun s _ => amitsur_d0_apply _ _ _⟩, fun s => ?_⟩
    rw [hY s (hw s), amitsur_d0_apply, map_sub, g.equivq]
  rcases w with v | u
  · exact top (inV G v) (fun s => Subgroup.mem_top (G := L.Gv v) s) y'' hy
  · obtain ⟨hz, Y, hY⟩ := hy
    obtain ⟨-, k1, k2⟩ := odKill l L G G0 h n x X D o
    obtain ⟨-, -, k3⟩ := odKill l L G G0 h n x X'' D'' o''
    obtain ⟨y, a1, a2, a3⟩ := (hur u x.A (D.Q (inU G u)) (k1 _) (k2 u)).2 (D''.Q (inU G u)) (g.fq (inU G u))
      (g.equivq (inU G u)) (hs _) y'' hz (fun s hs => (hY s hs).trans (sub_eq_zero.2 (k3 u s hs Y)))
    exact ⟨y, ⟨a1, 0, fun s hs => (a2 s hs).trans (sub_eq_zero.2 (k2 u s hs 0)).symm⟩, a3⟩
