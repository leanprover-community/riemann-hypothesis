module

public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormWeierstrassPSubEqOne
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotRedOfMem

@[expose] public section

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory.Honda

theorem norm_weierstrassP_sub_eq_one_of_good :
    ∀ (L : PeriodPair) (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (ι : ℂ ≃+* ℂ_[l]), ‖ι L.g₂‖ ≤ 1 → ‖ι L.g₃‖ ≤ 1 →
      ‖ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2‖ = 1 → ∀ u v : ℂ, u ∉ L.lattice → v ∉ L.lattice → u + v ∉ L.lattice →
      u - v ∉ L.lattice → ‖ι (L.weierstrassP u)‖ ≤ 1 → ‖ι (L.weierstrassP v)‖ ≤ 1 →
      ‖ι (L.weierstrassP (u + v))‖ ≤ 1 → ‖ι (L.weierstrassP (u - v))‖ ≤ 1 →
      ‖ι (L.weierstrassP u) - ι (L.weierstrassP v)‖ = 1 := by
  intro L l _ hl ι hg2 hg3 hD u v hu hv huv hmuv hpu hpv hpuv hpmuv
  have hgood : GlobalTheory.Klein.Good ι L 0 := by
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩
    · simp
    · simpa using hg2
    · simpa using hg3
    · rw [map_sub, map_pow, map_mul, map_pow, map_ofNat]; exact hD
  have hred : ∀ z, z ∉ L.lattice → ‖ι (L.weierstrassP z)‖ ≤ 1 → GlobalTheory.Klein.Red ι L 0 z :=
    fun z hz hp => ⟨hz, by simpa using hp⟩
  have h := GlobalTheory.Klein.norm_weierstrassP_sub_eq_one l ι L 0 hgood u v (hred u hu hpu) (hred v hv hpv)
    (hred _ huv hpuv) (hred _ hmuv hpmuv)
  simpa [map_sub] using h

end GlobalTheory.Honda
