module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsApplyEqOfNormal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.HD

theorem exists_hilbert_le_O (hR : RayField) (B : Base) (δ : FieldDat B.toPre) (hδ : δ.ray ≤ B.KsC) :
    ∃ M : IntermediateField ℚ ℂ, IsRayFieldIn B.host.φ₀ ⊤ M ∧
      ∀ z ∈ M, IsIntegral ℤ z → ∃ y : B.O, B.embLL (B.OtoLL y) = z := by
  obtain ⟨M, hM⟩ := exists_isRayFieldIn B.host.φ₀ hR (𝔮 := ⊤) top_ne_bot
  refine ⟨M, hM, fun z hz hI => ?_⟩
  have hle : M ≤ δ.ray := RayMono.le_of_isRayFieldIn_of_dvd _ _ _ _ _ _ (natIdeal_ne_bot (modulus_ne_zero B.toPre))
    (Ideal.dvd_iff_le.2 le_top) hM δ.isRay
  obtain ⟨x, hx, rfl⟩ := B.mem_KsC.1 (hδ (hle hz))
  have hx' : IsIntegral ℤ x :=
    (isIntegral_algHom_iff B.embLL.toIntAlgHom B.embLL.injective).1 hI
  obtain ⟨y, hy⟩ := B.O_full x hx hx'
  exact ⟨y, by rw [hy]⟩

theorem twistConductor_not_over_levelPrimes (B : Base) (T : TwDat B) (w : B.places.Pl) {v : HeightOneSpectrum (𝓞 B.host.E)} (hv : v ∈ T.Q w)
    (u : B.Word) (hp : (B.T u).Prime) : ¬ OverP B.host (B.T u) v := by
  intro ho
  obtain ⟨-, h1, -, h2⟩ := (T.psi_tw w).2.2.2 v fun h => ((T.psi_is w).ram v).1 h hv
  have := Examples₂.PlacesToy.prime_mem_unique v h1 hp (Ideal.absNorm_mem _) ho
  exact h2 (this ▸ .inr (.inr (.inr (.inr (.inl ⟨u, rfl⟩)))))

end GlobalTheory.Mem.HD
