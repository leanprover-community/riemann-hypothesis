module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.KappaZeroD
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private theorem isIntegral_entry_zero_zero_of_mem_kd {O K : Type} [CommRing O] [Field K] [Algebra O K] {Δ : K} {t : DX Δ}
    (ht : t ∈ KD Δ O) :
    IsIntegral O (((t : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 0 0) := by
  rw [KD, Subgroup.mem_subgroupOf, MonoidHom.mem_range] at ht
  obtain ⟨N, hN⟩ := ht
  rw [← hN, Matrix.GeneralLinearGroup.map_apply]
  exact (N.1 0 0).2

private theorem inv_mul_scal_entry_zero_zero_eq {K : Type} [Field K] {Δ : K} {z z' : Kˣ} {s s' : DX Δ}
    (hs : IsScal z s) (hs' : IsScal z' s') :
    (((s'⁻¹ * s : DX Δ) : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 0 0
      = algebraMap K (Lsq K Δ) ((z' : K)⁻¹ * z) := by
  have e : s = s' * (s'⁻¹ * s) := by group
  have hmat : Glob.mt s = Glob.mt s' * Glob.mt (s'⁻¹ * s) := by
    conv_lhs => rw [e]
    rfl
  unfold IsScal at hs hs'
  rw [hs, hs'] at hmat
  have e2 := congrFun (congrFun hmat 0) 0
  simp only [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.diagonal_apply_eq] at e2
  show Glob.mt (s'⁻¹ * s) 0 0 = _
  set M := Glob.mt (s'⁻¹ * s) 0 0
  have h1 : algebraMap K (Lsq K Δ) (z' : K)⁻¹ * algebraMap K (Lsq K Δ) (z' : K) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ z'.ne_zero, map_one]
  rw [map_mul]
  linear_combination (-(algebraMap K (Lsq K Δ) (z' : K)⁻¹)) * e2 + (-M) * h1

theorem UpperTheory.V.Z.Sym.Loc.fzdLaw : UpperTheory.V.Z.Sym.Loc.FzdLaw := by
  intro O K _ _ _ _ _ Δ hL χ hχ
  haveI := hL.frac
  refine ⟨?_, ?_⟩
  · intro g hg
    rw [fZD, dite_eq_right]
    rintro ⟨z, s, hs, hk⟩
    apply hg
    have hsZ : s ∈ ZD Δ := by
      rw [ZD, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
      refine ⟨z, Matrix.GeneralLinearGroup.ext fun i j => ?_⟩
      have h := congrFun (congrFun hs i) j
      rw [show (((s : DX Δ) : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) i j
        = Glob.mt s i j from rfl, h]
      simp [Matrix.scalar_apply]
    have e : g = s * (s⁻¹ * g) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hsZ hk
  · intro z s k hs hk
    have hex : ∃ z s', IsScal z s' ∧ s'⁻¹ * (s * k) ∈ KD Δ O :=
      ⟨z, s, hs, by rwa [inv_mul_cancel_left]⟩
    rw [fZD, dite_eq_left hex]
    obtain ⟨hs', hk'⟩ := hex.choose_spec.choose_spec
    set z' := hex.choose
    set s' := hex.choose_spec.choose
    have ht : s'⁻¹ * s ∈ KD Δ O := by
      have e : s'⁻¹ * s = (s'⁻¹ * (s * k)) * k⁻¹ := by group
      rw [e]
      exact mul_mem hk' (inv_mem hk)
    have ht' : s⁻¹ * s' ∈ KD Δ O := by
      have e : s⁻¹ * s' = (s'⁻¹ * s)⁻¹ := by group
      rw [e]
      exact inv_mem ht
    have i1 := isIntegral_entry_zero_zero_of_mem_kd ht
    rw [inv_mul_scal_entry_zero_zero_eq hs hs'] at i1
    have i2 := isIntegral_entry_zero_zero_of_mem_kd ht'
    rw [inv_mul_scal_entry_zero_zero_eq hs' hs] at i2
    let f : K →ₐ[O] Lsq K Δ := IsScalarTower.toAlgHom O K (Lsq K Δ)
    have hf : Function.Injective f := (algebraMap K (Lsq K Δ)).injective
    rw [show algebraMap K (Lsq K Δ) ((z' : K)⁻¹ * z) = f ((z' : K)⁻¹ * z) from rfl,
      isIntegral_algHom_iff f hf, IsIntegrallyClosed.isIntegral_iff (K := K)] at i1
    rw [show algebraMap K (Lsq K Δ) ((z : K)⁻¹ * z') = f ((z : K)⁻¹ * z') from rfl,
      isIntegral_algHom_iff f hf, IsIntegrallyClosed.isIntegral_iff (K := K)] at i2
    obtain ⟨a, ha⟩ := i1
    obtain ⟨b, hb⟩ := i2
    have hab : a * b = 1 := by
      apply IsFractionRing.injective O K
      rw [map_mul, ha, hb, map_one]
      field_simp
    have hu := hχ ⟨a, b, hab, by rw [mul_comm]; exact hab⟩
    have hmap : (Units.map (algebraMap O K : O →* K)) ⟨a, b, hab, by rw [mul_comm]; exact hab⟩
        = z'⁻¹ * z := Units.ext (by simp [ha])
    rw [hmap, map_mul, map_inv, inv_mul_eq_one] at hu
    rw [hu]
