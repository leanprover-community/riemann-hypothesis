module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.BaseBc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.MapsBc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.RingBc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.SinfIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilLam
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

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.aut_bc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (n : ℕ) (O O' : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] [CommRing O'] [IsLocalRing O'] [Algebra ℤ_[l] O'] [Algebra O O'] [IsScalarTower ℤ_[l] O O'] [IsLocalHom (algebraMap O O')] [Module.Finite O O'] [Module.Free O O'] (r : Resid G0.frame O n) (r' : Resid G0.frame O' n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] [IsCO O' (Til O O' B)] (u : Pair r B) (u' : Pair r' (Til O O' B)) (J : Ideal B) (D : ℕ) (T : TWGrp G0) (_A : TWAut u J Empty D T), RBC r r' → u.Maps (Til.ι O O' B) u'.D u'.ψ → ∃ A' : TWAut u' (J.map (Til.ι O O' B)) Unit D T, A'.b.lam (MvPowerSeries.X (.inl ())) = Til.s O O' B := by
  intro l _ L G0 n O O' _ _ _ _ _ _ _ _ _ _ _ _ _ r r' B _ _ _ _ u u' J D T A hr hu
  obtain ⟨τ, hτ, hs⟩ := UpperTheory.V.Pa.BC.til_lam O O' D
  obtain ⟨τS, hS⟩ := UpperTheory.V.Pa.BC.sinf_iso l O O' D T.q n τ hτ
  obtain ⟨b', hb⟩ := UpperTheory.V.Pa.BC.base_bc l L G0 n O O' r r' B u u' J D A.b τ hr hu hτ
  have hA := fun N => UpperTheory.V.Pa.BC.ring_bc l L G0 n O O' r r' B u u' J D A.b b' τ (T.GN N) (T.h N) T.q A.ut N τS
    (A.A N) hr hu hb hS
  choose A' hA' using hA
  have hm := fun N => UpperTheory.V.Pa.BC.maps_bc l L G0 n O O' r r' B u u' J D A.b b' τ (T.GN N) (T.h N) T.q A.ut N τS
    (A.A N) (A' N) (T.Nq N) (T.ph N) (T.ta N) A.ex (A.m N) hr hu hb hS (hA' N)
  refine ⟨⟨b', fun j i => algebraMap O O' (A.ut j i), ?_, A', A.ex, fun N => (hm N).some⟩, ?_⟩
  · intro j i
    rw [hr.1 i, ← ResidueField.map_residue, A.ut_res]
    rfl
  · obtain ⟨hb⟩ := hb
    show b'.lam _ = _
    rw [← hs, hb.lam, Til.map_s]
