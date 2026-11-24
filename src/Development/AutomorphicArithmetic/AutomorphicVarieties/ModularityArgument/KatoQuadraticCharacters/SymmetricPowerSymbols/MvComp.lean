module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ComapLtOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.DifB
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.KaB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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

noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4

namespace UpperTheory.V.Z.Kato.Sym

private theorem ka_pow {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (m : ℕ) (hm : 0 < m)
    (θ : Kb X) (u : X.K) (hu : u ≠ 0) (hθ : θ ^ m = io X u) (h : RingAut (Kb X)) (hh : InD X h) (n : ℕ) :
    ka X m (θ ^ n) h = (n : ZMod m) * ka X m θ h := by
  obtain ⟨-, -, hlg, -, -, -, -⟩ := lgB Ω ε X m hm
  induction n with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul, ka, map_one]
    exact hlg 1 1 0 one_ne_zero (by simp)
  | succ k ih =>
    have hk : (θ ^ k) ^ m = io X (u ^ k) := by
      rw [← pow_mul, mul_comm, pow_mul, hθ, map_pow]
    rw [pow_succ, (kaB Ω ε X m hm (θ ^ k) (u ^ k) (pow_ne_zero _ hu) hk).2.2.2.2.2 θ u hu hθ h hh, ih]
    push_cast
    ring

theorem mvComp : MvComp := by
  intro Ω _ _ _ ε X m hm τ τ' s s' hadm hadm' u v P Q R hP hQ hR f f' hf hf'
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨σ, hσ, θ, hθ, hkθ⟩ := hf
  obtain ⟨σ', hσ', θ', hθ', hkθ'⟩ := hf'
  obtain ⟨-, -, -, -, -, -, hcyc⟩ := lgB Ω ε X m hm
  have f0 : (f : X.K) ≠ 0 := f.ne_zero
  have τf0 : τ' (f : X.K) ≠ 0 := by simpa using f0
  have r1 : (σ' θ) ^ m = io X (τ' (f : X.K)) := by
    rw [← map_pow, hθ, hσ']
  have hPτ := mvPt Ω ε X m hm τ s hadm σ hσ u v P hP
  have hA' := mvPt Ω ε X m hm τ' s' hadm' σ' hσ' (τ u) (τ v) _ hPτ
  have hB' := mvPt Ω ε X m hm τ' s' hadm' σ' hσ' (τ u) (τ v) Q hQ
  have D1 := difB Ω ε X m hm (τ u) (τ v) _ Q hPτ hQ
  have D2 := difB Ω ε X m hm (τ' (τ u)) (τ' (τ v)) _ _ hA' hB'
  have KB := kaB Ω ε X m hm θ f f0 hθ
  set k := (cyc m s').val with hkdef
  have KP := kaB Ω ε X m hm ((σ' θ) ^ k) (τ' (f : X.K) ^ k) (pow_ne_zero _ τf0)
    (by rw [← pow_mul, mul_comm, pow_mul, r1, map_pow])
  have hA : Pt.mv (σ' * σ) (cyc m (s' * s)) P = Pt.mv σ' (cyc m s') (Pt.mv σ (cyc m s) P) := by
    rw [(hcyc s' s).1]
    simp only [Pt.mv]
    congr 1
    funext h
    rw [show σ⁻¹ * (σ'⁻¹ * h * σ') * σ = (σ' * σ)⁻¹ * h * (σ' * σ) by group]
    ring
  refine ⟨σ' * σ, fun x => ?_, (σ' θ) ^ k * θ', ?_, fun h hh => ?_⟩
  · show σ' (σ (io X x)) = io X (τ' (τ x))
    rw [hσ x, hσ']
  · simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, mul_pow, ← hθ']
    rw [← pow_mul, mul_comm k m, pow_mul, r1]
    rfl
  · obtain ⟨hin, hconj⟩ := KB.2.2.2.2.1 σ' τ' s' hadm' hσ' h hh
    rw [KP.2.2.2.2.2 θ' f' f'.ne_zero hθ' h hh, ka_pow X m hm (σ' θ) (τ' (f : X.K)) τf0 r1 h hh k,
      hconj, hkθ _ hin, hkθ' h hh, hA, D2.2.2.2.1 R hR h hh, D1.2.2.2.2.2.2 τ' s' hadm' σ' hσ' h hh,
      hkdef, ZMod.natCast_zmod_val]
    ring

end UpperTheory.V.Z.Kato.Sym

end
