module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueLocalOfFam
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluedFormOrthogonality

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.GluingBases

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem form_U_orth {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {u z : V} (hu : u ∈ U)
    (hz : z ∈ orthK h U) : h u z = 0 := by
  have hz' : z ∈ ⨅ w ∈ U, LinearMap.ker (h w) := hz
  simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hz'
  exact hz' u hu

theorem form_orth_U {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {U : Submodule K V} {u z : V}
    (hu : u ∈ U) (hz : z ∈ orthK h U) : h z u = 0 :=
  hs.eq_iff.1 (form_U_orth hu hz)

theorem glue_inl_inl {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {U : Submodule K V}
    {𝔭 : Ideal (𝓞 F)} {n m : ℕ} {b : Fin n → V} {a : Fin n → 𝓞 F} {π : 𝓞 F} {w : Fin m → V}
    {τ : Fin n → Fin m} (hbU : ∀ i, b i ∈ U) (hbo : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (hwW : ∀ j, w j ∈ orthK h U) (hwo : ∀ j k, j ≠ k → h (w j) (w k) = 0)
    (hτ : ∀ i k, vF 𝔭 (a i) ≠ 0 → vF 𝔭 (a k) ≠ 0 → τ i = τ k → i = k) {i i' : Fin n} (hii : i ≠ i') :
    h (glueFam K 𝔭 b a π w τ (Sum.inl i)) (glueFam K 𝔭 b a π w τ (Sum.inl i')) = 0 := by
  simp only [glueFam, Sum.elim_inl]
  split_ifs with h1 h2 h2
  · exact hbo _ _ hii
  · simp only [map_smulₛₗ, map_add (f := _), add_zero, smul_eq_mul, mul_zero, hbo _ _ hii, form_U_orth (hbU i) (hwW _)]
  · simp only [map_smulₛₗ, map_add (f := _), LinearMap.add_apply, LinearMap.smul_apply, add_zero, smul_eq_mul, mul_zero, hbo _ _ hii, form_orth_U hs (hbU i') (hwW _)]
  · have hτ' : τ i ≠ τ i' := fun e => hii (hτ i i' h1 h2 e)
    simp only [map_smulₛₗ, map_add (f := _), LinearMap.add_apply, LinearMap.smul_apply, add_zero, smul_eq_mul, mul_zero, hbo _ _ hii, form_U_orth (hbU i) (hwW _),
      form_orth_U hs (hbU i') (hwW _), hwo _ _ hτ']

theorem glue_inl_w {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V}
    {𝔭 : Ideal (𝓞 F)} {n m : ℕ} {b : Fin n → V} {a : Fin n → 𝓞 F} {π : 𝓞 F} {w : Fin m → V}
    {τ : Fin n → Fin m} (hbU : ∀ i, b i ∈ U) (hwW : ∀ j, w j ∈ orthK h U)
    (hwo : ∀ j k, j ≠ k → h (w j) (w k) = 0) {i : Fin n} {j : Fin m}
    (hj : vF 𝔭 (a i) ≠ 0 → τ i ≠ j) :
    h (glueFam K 𝔭 b a π w τ (Sum.inl i)) (w j) = 0 := by
  simp only [glueFam, Sum.elim_inl]
  split_ifs with h1
  · exact form_U_orth (hbU i) (hwW j)
  · simp only [map_smulₛₗ, map_add (f := _), LinearMap.add_apply, LinearMap.smul_apply, add_zero, smul_eq_mul, mul_zero, form_U_orth (hbU i) (hwW j), hwo _ _ (hj h1)]

end Formalism.L2.SG.Pf.GluedFormOrthogonality
