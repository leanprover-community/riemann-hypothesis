module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.KappaZeroD
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ExistsOfGOrbNe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ExistsUnitOneAddGenerator
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.MemRangeIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.OrbitImp
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Loc.oneD : UpperTheory.V.Z.Sym.Loc.OneD := by
  intro O K _ _ _ _ _ Δ τ L hτ γ j h1 h2 hγ hD
  obtain ⟨φ, p1, p2, p3, p4⟩ := dIso O K Δ L
  obtain ⟨j', q1, q2, q3⟩ := p4 τ γ j h1 h2
  have sc : ∀ z : Kˣ, IsScal z (φ.symm (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) := fun z => (p2 _ _).2 (by simp)
  have hZ : ∀ g, g ∈ ZD Δ ⊔ KD Δ O ↔ φ g ∈ ZK O K := fun g => by
    constructor
    · intro h
      refine (sup_le ?_ ?_ : ZD Δ ⊔ KD Δ O ≤ (ZK O K).comap φ.toMonoidHom) h
      · rintro s ⟨z, hz⟩
        exact Subgroup.mem_sup_left ⟨z, ((p2 z s).1 (congrArg Units.val hz).symm).symm⟩
      · exact fun k hk => Subgroup.mem_sup_right ((p1 k).2 hk)
    · intro h
      obtain ⟨z, k, e⟩ := mem_ZK.1 h
      rw [← φ.symm_apply_apply g, e, map_mul]
      exact mul_mem (Subgroup.mem_sup_left ⟨z, Units.ext (sc z).symm⟩) (Subgroup.mem_sup_right ((p1 _).1 (by rw [φ.apply_symm_apply]; exact ⟨k, rfl⟩)))
  obtain ⟨a, ha⟩ := exists_a (K := K) (τ := τ)
  have ea : j a = γ := φ.injective (by rw [q3]; exact Units.ext (by rw [← q1, ← ha]; rfl))
  have back : ∀ y t x k, k ∈ ZK O K → φ y = jU j' t * x * k → ∃ u ∈ ZD Δ ⊔ KD Δ O, y = j t * φ.symm x * u := fun y t x k hk e =>
    ⟨φ.symm k, (hZ _).2 (by simpa using hk), φ.injective (by simp [e, q3])⟩
  obtain ⟨k₀, hk₀⟩ := (p1 γ).2 hγ
  obtain ⟨G1, G2⟩ := oneG O K Δ τ L j' q2 (fun s t => ⟨k₀ s t, by rw [q1, ← hk₀]; rfl⟩) hD
  have main : ∀ z : (Etau K τ)ˣ, ((z : Etau K τ) = ω ∨ (z : Etau K τ) = 1 + ω) → ∀ y, y⁻¹ * j z * y ∈ ZD Δ ⊔ KD Δ O →
      ∃ t, ∃ u ∈ ZD Δ ⊔ KD Δ O, y = j t * u := fun z hz y hy => by
    obtain ⟨t, k, hk, e⟩ := ((G2 z hz).2 (φ y)).1 (by simpa [q3] using (hZ _).1 hy)
    obtain ⟨u, hu, e'⟩ := back y t 1 k hk (by simpa using e)
    exact ⟨t, u, hu, by simpa using e'⟩
  refine ⟨?_, ea ▸ main a (.inl ha), fun z hz => ⟨(p1 _).1 (q3 z ▸ (G2 z (.inr hz)).1), main z (.inr hz)⟩⟩
  rw [← G1]
  ext t
  rw [Subgroup.mem_comap, Subgroup.mem_comap, hZ, q3]
