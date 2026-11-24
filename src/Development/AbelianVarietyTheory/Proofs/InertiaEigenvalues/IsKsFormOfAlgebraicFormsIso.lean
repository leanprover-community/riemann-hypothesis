module

public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.RatDatOfReal
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Formalism.IndefR.NX

namespace GlobalTheory

theorem isKsForm_of_formsIso {LL Ks Ks' WL WL' G G' : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks]
    [Algebra Ks LL] [Field Ks'] [NumberField Ks'] [Algebra Ks' LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL]
    [IsScalarTower Ks LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] [AddCommGroup WL'] [Module LL WL']
    [Module Ks' WL'] [IsScalarTower Ks' LL WL'] [Module (𝓞 Ks') WL'] [IsScalarTower (𝓞 Ks') Ks' WL']
    {W W' : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    [∀ σ, NormedAddCommGroup (W' σ)] [∀ σ, InnerProductSpace ℂ (W' σ)] [Group G] [Group G']
    (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G) (A' : Formalism.IndefR.Arith.FormsL LL Ks' WL' W' G') :
    FormsIso A A' → A'.IsKsForm → A.IsKsForm := by
  intro f hA'
  obtain ⟨n, b, hmem, _hKi, hKs, hLi, hLs⟩ := hA'
  have hmem' : ∀ i, f.e.symm (b i) ∈ A.WK := fun i => (f.wk _).2 (by simpa using hmem i)
  have hLi' : LinearIndependent LL (fun i => f.e.symm (b i)) :=
    hLi.map' f.e.symm.toLinearMap (LinearEquiv.ker _)
  refine ⟨n, fun i => f.e.symm (b i), hmem', ?_, ?_, hLi', ?_⟩
  · refine LinearIndependent.restrict_scalars (K := LL) ?_ hLi'
    intro r s h
    have h' : algebraMap Ks LL r = algebraMap Ks LL s := by
      simpa [Algebra.algebraMap_eq_smul_one] using h
    exact (algebraMap Ks LL).injective h'
  · apply le_antisymm
    · exact Submodule.span_le.2 (Set.range_subset_iff.2 hmem')
    · intro y hy
      have hy' : f.e y ∈ Submodule.span Ks' (Set.range b) := by rw [hKs]; exact (f.wk y).1 hy
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Ks').1 hy'
      have hyeq : y = ∑ i, f.eK.symm (c i) • f.e.symm (b i) := by
        have : y = f.e.symm (∑ i, c i • b i) := by rw [hc]; simp

        rw [this, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← algebraMap_smul LL (c i) (b i), LinearEquiv.map_smul, ← algebraMap_smul LL (f.eK.symm (c i)),
          ← f.eK_LL, RingEquiv.apply_symm_apply]
      rw [hyeq]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · have : Set.range (fun i => f.e.symm (b i)) = f.e.symm '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, show (⇑f.e.symm : WL' → WL) = ⇑(f.e.symm : WL' →ₗ[LL] WL) from rfl, Submodule.span_image, hLs,
      Submodule.map_top, LinearEquiv.range]

end GlobalTheory
