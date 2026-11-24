module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
public import Development.AutomorphicArithmetic.LocalEmbeddings.CoinvFin
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
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.LevelModule
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Pa.Lev.isoFix :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (Y : Type) [AddCommGroup Y] [Module ℂ Y] (π : Representation ℂ (GL (Fin n) k) Y) (σ : SmIrr (GL (Fin n) k)) (I : Subgroup (GL (Fin n) k)), IsCompact (I : Set (GL (Fin n) k)) → IsoSum π ⊤ σ → ∀ y ∈ fixd π I, y ∈ ⨆ f : {f : σ.V →ₗ[ℂ] Y // ∀ g v, f (σ.ρ g v) = π g (f v)}, (fixd σ.ρ I).map f.1 := by
  intro k _ _ _ _ n Y _ _ π σ I hI hs y hy
  refine UpperTheory.Dv.CoinvFin.mem_of_span π hI
    {w | ∃ f : σ.V →ₗ[ℂ] Y, (∀ g v, f (σ.ρ g v) = π g (f v)) ∧ ∃ v, w = f v} _ ?_ ?_ hy
  · rintro _ ⟨f, hf, v, rfl⟩
    refine ⟨UpperTheory.Dv.CoinvFin.stab σ.ρ v, σ.smooth v, fun K' hK' _ => ?_⟩
    refine Submodule.mem_iSup_of_mem ⟨f, hf⟩ ⟨UpperTheory.Dv.CoinvFin.av σ.ρ I K' v, UpperTheory.Dv.CoinvFin.av_fixed σ.ρ I K' hK', ?_⟩

    simp only [UpperTheory.Dv.CoinvFin.av, map_sum, hf]
  · refine (iSup_le fun f => ?_ : _ ≤ Submodule.span ℂ _) (hs Submodule.mem_top)
    rintro _ ⟨v, rfl⟩
    exact Submodule.subset_span ⟨f.1, f.2.1, v, rfl⟩
