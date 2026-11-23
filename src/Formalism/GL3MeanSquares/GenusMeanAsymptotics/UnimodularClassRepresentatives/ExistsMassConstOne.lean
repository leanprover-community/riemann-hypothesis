module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlphaStdOneNeZero
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsNeZeroOfIsLattice
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsClassRepsMap
import Formalism.HermitianLattices.HermitianLatticesProofs.MassBasic
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace RankOne

open Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem trace_pos {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : IsTotPosDef h) :
    ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x) := by
  intro x hx
  have hsum := trace_eq_sum_embeddings ℂ (K := ℚ) (x := h x x)
  have hre : ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) = ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re := by
    have := congrArg Complex.re hsum
    simpa [Complex.re_sum] using this
  have hne : Nonempty (K →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  have hpos : 0 < ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re :=
    Finset.sum_pos (fun σ _ => hd x hx σ.toRingHom) Finset.univ_nonempty
  exact_mod_cast hre ▸ hpos

theorem exists_model [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hd : IsTotPosDef h) (h1 : finrank K V = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) :
    ∃ (h' : K →ₗ⋆[K] K →ₗ[K] K) (A : Submodule (𝓞 K) K), h' 1 1 ≠ 0 ∧ Submodule.IsFullLattice K A ∧
      (∃ s, IsClassReps h' A s) ∧ mass h' A = mass h L := by
  let b := Module.finBasisOfFinrankEq K V h1
  let φ : V ≃ₗ[K] K := b.equivFun.trans (LinearEquiv.funUnique (Fin 1) K K)
  let h' : K →ₗ⋆[K] K →ₗ[K] K := (h.comp φ.symm.toLinearMap).compl₂ φ.symm.toLinearMap
  have hh' : ∀ x y, h' (φ x) (φ y) = h x y := by
    intro x y
    simp [h']
  have htr := trace_pos hd
  obtain ⟨hex, -, -⟩ := Formalism.HermitianLatticesTheory.massBasic K V h hs htr L hL
  obtain ⟨hex', hm⟩ := mass_mapE φ hh' hex
  refine ⟨h', mapE φ L, ?_, isFullLattice_mapE φ hL, hex', hm⟩
  have h0 : φ.symm 1 ≠ 0 := by simp
  intro hz
  have := htr _ h0
  have hz' : h (φ.symm 1) (φ.symm 1) = 0 := by simpa [h'] using hz
  rw [hz', map_zero] at this
  exact lt_irrefl _ this

end RankOne

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem exists_massConst_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) :
    ∃ c : ℝ, 0 < c ∧ MassConst K F 1 c := by
  obtain ⟨h₀, hh⟩ : ∃ h₀ : K →ₗ⋆[K] K →ₗ[K] K, ∀ x y, h₀ x y = star x * y :=
    ⟨LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => star x * y)
      (fun x y z => by simp [add_mul]) (fun a x y => by simp [smul_eq_mul, mul_assoc, starRingEnd_apply])
      (fun x y z => by simp [mul_add]) (fun a x y => by simp [smul_eq_mul, mul_left_comm]),
      fun _ _ => rfl⟩
  have hs₀ : h₀.IsSymm := by
    first
      | (intro x y; simp [hh, starRingEnd_apply, mul_comm])
      | (constructor; intro x y; simp [hh, starRingEnd_apply, mul_comm])
  have hd₀ : IsTotPosDef h₀ := by
    intro x hx φ
    have hx' : φ x ≠ 0 := (map_ne_zero φ).mpr hx
    have : φ (h₀ x x) = ((Complex.normSq (φ x) : ℝ) : ℂ) := by
      rw [hh, map_mul, hK.2.1 φ x, Complex.normSq_eq_conj_mul_self]
    rw [this, Complex.ofReal_re]
    exact Complex.normSq_pos.mpr hx'
  have hn₀ : h₀ 1 1 ≠ 0 := by simp [hh]
  set L₀ : Submodule (𝓞 K) K := Submodule.span (𝓞 K) {(1 : K)}
  have hL₀ : Submodule.IsFullLattice K L₀ :=
    { toIsLattice := Submodule.IsLattice.of_fg K (Submodule.fg_span_singleton _)
      span_eq_top := RankOne.span_eq_top_of_ne_zero (Submodule.subset_span rfl) one_ne_zero }
  obtain ⟨hex₀, -, hpos₀⟩ := Formalism.HermitianLatticesTheory.massBasic K K h₀ hs₀
    (RankOne.trace_pos hd₀) L₀ hL₀
  refine ⟨Formalism.HermitianLatticesTheory.mass h₀ L₀, hpos₀, ?_⟩
  intro V _ _ _ _ _ h L hs hd h1 hL hLi
  obtain ⟨h', A, hn', hA, -, hm⟩ := RankOne.exists_model hs hd h1 hL
  have hlam : lamG F h L = 1 := by
    unfold lamG
    exact (tprod_congr fun p => localFactor_rank_one hK hF hs hd hL hLi h1 p.2).trans tprod_one
  rw [hlam, mul_one, ← hm]
  exact RankOne.mass_eq_of_lattices hn₀ hn' hL₀ hA hex₀

end Formalism.HermitianLattices.Ext.L3
