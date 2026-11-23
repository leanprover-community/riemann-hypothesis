module

import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RayClassConeParametrization
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

namespace GlobalTheory.NatSmulMemLattice

open NumberField

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ (n : ℕ) (a : 𝓞 E), 0 < n ∧ (a : E) = (n : E) * c := by
  apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_nat_mul_integer <;> assumption

theorem exists_nat_smul_mem {E W : Type} [Field E] [NumberField E] [AddCommGroup W] [Module E W]
    [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] (L : Submodule (𝓞 E) W)
    (hL : Submodule.span E (L : Set W) = ⊤) (v : W) :
    ∃ d : ℕ, 0 < d ∧ (d : 𝓞 E) • v ∈ L := by
  have hv : v ∈ Submodule.span E (L : Set W) := hL ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [smul_add, Nat.cast_mul]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact L.smul_mem _ hx
    · rw [mul_smul]
      exact L.smul_mem _ hy
  | smul c x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨n, e, hn, he⟩ := exists_nat_mul_integral c
    refine ⟨a * n, Nat.mul_pos ha hn, ?_⟩
    have key : ((a * n : ℕ) : 𝓞 E) • c • x = e • (a : 𝓞 E) • x := by
      rw [← algebraMap_smul E e, ← algebraMap_smul E (a : 𝓞 E),
        ← algebraMap_smul E ((a * n : ℕ) : 𝓞 E), smul_smul, smul_smul]
      congr 1
      have he' : algebraMap (𝓞 E) E e = (n : E) * c := he
      rw [he', map_natCast, map_natCast, Nat.cast_mul]
      ring
    rw [key]
    exact L.smul_mem _ hx

theorem exists_nat_smul_mem_lattice {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (v : Formalism.BasicNotions.HSpace.V V) :
    ∃ d : ℕ, 0 < d ∧ (d : 𝓞 (Formalism.BasicNotions.D7.host D).E) • v ∈ Formalism.BasicNotions.HSpace.L0 V :=
  by
    let E := (Formalism.BasicNotions.D7.host D).E
    let f := (V.hT v).restrictScalars (𝓞 E)
    obtain ⟨d, hd, hint⟩ := FractionalIdeal.isFractional_of_fg
      (S := nonZeroDivisors (𝓞 E)) (V.standardTuple_isLattice.fg.map f)
    have hd0 : (d : E) ≠ 0 := by simpa using nonZeroDivisors.ne_zero hd
    obtain ⟨n, a, hn, ha⟩ := exists_nat_mul_integral (d : E)⁻¹
    refine ⟨n, hn, ?_⟩
    rw [← V.baseLattice_isUnimodular]
    change (n : 𝓞 E) • v ∈ Formalism.E.hdual V.hT V.L0
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap]
    intro y hy
    obtain ⟨b, hb⟩ := hint (V.hT v y) ⟨y, hy, rfl⟩
    have hb' : (b : E) = (d : E) * V.hT v y := hb
    have hab : ((a * b : 𝓞 E) : E) = (n : E) * V.hT v y := by
      change (a : E) * (b : E) = _
      rw [ha, hb']
      field_simp
    have hs : IsIntegral ℤ (star ((n : E) * V.hT v y)) := by
      rw [← hab]
      exact (a * b).2.map (starRingEnd E).toIntAlgHom
    apply Submodule.mem_one.2
    refine ⟨⟨_, ?_⟩, rfl⟩
    change IsIntegral ℤ _
    have hh := V.herm.eq y v
    simp only [star_mul, star_natCast] at hs
    have hh' : star (V.hT v y) = V.hT y v := by
      rw [← hh]
      exact star_star _
    rw [hh'] at hs
    simpa [map_smul, Algebra.smul_def, mul_comm] using hs

end GlobalTheory.NatSmulMemLattice
