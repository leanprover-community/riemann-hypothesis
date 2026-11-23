module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SplitAtOf
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsFracOfFixed
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.GmapLocEqOfFrame
import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

theorem local_span_holds : LocSpan := by
  intro K F V _ _ _ _ _ _ _ _ _ _ hK hF P hP n b v
  have hPp := hP.isPrime
  constructor
  · intro hv
    obtain ⟨s, hs, hsv⟩ := Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp hv
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hsv
    have hs0 := algebraMap_ne_zero_of_mem_hcompl hPp hs
    refine ⟨fun i => algebraMap (𝓞 K) K (c i) / algebraMap (𝓞 K) K s,
      fun i => div_mem_locRing hPp (c i) hs, ?_⟩
    have e : v = (algebraMap (𝓞 K) K s)⁻¹ • (algebraMap (𝓞 K) K s • v) := by
      rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [e, algebraMap_smul, ← hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul K (c i) (b i), smul_smul]
    simp only [div_eq_inv_mul]
  · rintro ⟨d, hd, rfl⟩
    refine Submodule.sum_mem _ fun i _ => smul_mem_loc hPp (hd i) ?_
    exact Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem jordan_span_holds :
    ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
      [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
      (L : Submodule (𝓞 K) V), Submodule.IsFullLattice K L → ∀ 𝔭 : Ideal (𝓞 F),
      𝔭.IsMaximal → ∀ (n : ℕ) (b : Fin n → V),
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L →
        Submodule.span K (Set.range b) = ⊤ := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ L hL 𝔭 h𝔭 n b hb
  letI : Submodule.IsFullLattice K L := hL
  rw [eq_top_iff, ← Submodule.IsFullLattice.span_eq_top (A := K) (M := L), Submodule.span_le]
  intro x hx
  have hx' : x ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) := by
    rw [hb]
    exact LocF.le_locF 𝔭 L hx
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff h𝔭.isPrime _ x).mp hx'
  have ht0 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
    intro h0
    apply ht
    have h1 : algebraMap (𝓞 F) (𝓞 K) t = 0 :=
      FaithfulSMul.algebraMap_injective (𝓞 K) K (by rw [h0, map_zero])
    have h2 : t = 0 := FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K) (by rw [h1, map_zero])
    rw [h2]
    exact 𝔭.zero_mem
  have hmem := Submodule.span_le_restrictScalars (𝓞 K) K (Set.range b) htx
  have e : x = (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹ •
      (algebraMap (𝓞 F) (𝓞 K) t • x) := by
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) x, smul_smul, inv_mul_cancel₀ ht0, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ hmem

end Formalism.L2.SG.Pf.G3
