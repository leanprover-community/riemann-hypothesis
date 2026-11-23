module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.LocallyConstantFinite.LcFin
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.KZ GlobalTheory.K4 Polynomial UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PE

theorem UpperTheory.V.Z.Kato.Sym.PE.integ :
    UpperTheory.V.Z.Kato.Sym.PE.Integ := by
  intro Ω _ _ _ ε X m hm u z hu hz
  have key : ∀ w : X.K, IsU X w → (pj X).IsIntegralElem (io X w) := by
    intro w hw
    let φ : Polynomial Ω →+* X.K := (aeval X.jK).toRingHom
    have hmem : w ∈ (integralClosure (Subring.closure (φ.range : Set X.K)) X.K).toSubring := by
      rw [← iInf_valuationSubring_superset, Subring.mem_iInf]
      rintro ⟨V, hV⟩
      have hov : X.OverY V := ⟨fun c => hV ⟨C c, by simp [φ]⟩, hV ⟨Polynomial.X, by simp [φ]⟩⟩
      exact (V.valuation_le_one_iff w).1 (hw.2 V hov).le
    obtain ⟨p, hp, hpw⟩ := hmem
    have hle : Subring.closure (φ.range : Set X.K) ≤ φ.range := Subring.closure_le.2 subset_rfl
    have hlift : p.map (algebraMap (Subring.closure (φ.range : Set X.K)) X.K) ∈ lifts φ := by
      rw [lifts_iff_coeff_lifts]
      intro n
      rw [coeff_map]
      exact RingHom.mem_range.1 (hle (p.coeff n).2)
    obtain ⟨Q, hQ, -, hQm⟩ := lifts_and_degree_eq_and_monic hlift (hp.map _)
    refine ⟨Q, hQm, ?_⟩
    show eval₂ ((io X).comp φ) (io X w) Q = 0
    rw [← hom_eval₂, ← eval_map, hQ, eval_map, hpw, _root_.map_zero]
  have hu0 : io X u ≠ 0 := (_root_.map_ne_zero _).2 hu.1
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hz
    exact hu0 hz.symm
  have hinv : IsU X u⁻¹ := ⟨inv_ne_zero hu.1, fun W hW => by rw [map_inv₀, hu.2 W hW, inv_one]⟩
  refine ⟨hz0, ?_, ?_⟩
  · letI := (pj X).toAlgebra
    refine IsIntegral.of_pow hm ?_
    rw [hz]
    exact key u hu
  · letI := (pj X).toAlgebra
    refine IsIntegral.of_pow hm ?_
    rw [inv_pow, hz, ← map_inv₀]
    exact key _ hinv
