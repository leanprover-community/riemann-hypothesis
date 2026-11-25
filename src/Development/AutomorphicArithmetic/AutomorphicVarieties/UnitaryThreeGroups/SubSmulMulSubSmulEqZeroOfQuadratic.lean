module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.RhoKApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.ExistsQuadraticGaussSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.TorsionOrderFrobenius.QuadMu
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.U3.EtaMu

private theorem cls_eq_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {N : ℕ} [NeZero N] (s : G ℚ Ω)
    (h : ∀ ζ : Ω, ζ ^ N = 1 → s ζ = ζ) : Chr.cls ℚ Ω N s = 1 := by
  have key : ∀ t ∈ rootsOfUnity N Ω,
      (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) (t : Ω) = (t : Ω) ^ (1 : ZMod N).val := by
    intro t ht
    have htN : (t : Ω) ^ N = 1 := by
      rw [mem_rootsOfUnity] at ht
      rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
    change s (t : Ω) = _
    rw [h _ htN, ZMod.val_one_eq_one_mod]
    rcases Nat.lt_or_ge 1 N with hN | hN
    · rw [Nat.mod_eq_of_lt hN, pow_one]
    · have hN1 : N = 1 := by
        have := NeZero.ne N
        omega
      rw [hN1] at htN ⊢
      rw [Nat.mod_self, pow_zero]
      simpa using htN
  apply Units.ext
  rw [Units.val_one]
  exact (modularCyclotomicCharacter.unique Ω (Chr.card_roots ℚ Ω N) _ key).symm

end UpperTheory.V.U3.EtaMu

open UpperTheory.V.U3.EtaMu in
theorem UpperTheory.V.U3.eta_killsMu :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ), Af.KillsMu (discr K).natAbs D.η ∧ 1 ≤ (discr K).natAbs ∧ Af.KillsMu N (Chr.dirG ℚ Ω ψ) ∧ Af.KillsMu N (Chr.dirG ℚ Ω (comp l ψ)) := by
  intro Ω _ _ _ K _ _ _ l _ c N _ e ψ D
  refine ⟨?_, Int.natAbs_pos.mpr (discr_ne_zero K), ?_, ?_⟩
  · intro s hs
    rw [← MonoidHom.mem_ker, D.η_ker]
    exact UpperTheory.V.Sd.Tw.quadMu K Ω D.gd.quad s (fun ζ hζ => by simpa using hs ζ hζ)
  · intro s hs
    simp only [Chr.dirG, MonoidHom.comp_apply, cls_eq_one s hs, map_one]
  · intro s hs
    simp only [Chr.dirG, MonoidHom.comp_apply, cls_eq_one s hs, map_one]
