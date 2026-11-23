module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.LocallyConstantFinite.LcFin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpec
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

open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

namespace UpperTheory.V.Z.Kato.Sym.PE

theorem kaU : KaU := by
  intro Ω _ _ _ ε X m hm θ hθ g h hgz hhz hgm hhm
  haveI : NeZero m := NeZero.of_pos hm
  obtain ⟨hprim, hrep, hlg, -⟩ := lgB Ω ε X m hm
  have hpow : zt X m ^ m = 1 := hprim.pow_eq_one
  have hgθ : g θ = zt X m ^ (ka X m θ g).val * θ := hrep (g θ) θ hθ (by rw [← map_pow, hgm])
  have hhθ : h θ = zt X m ^ (ka X m θ h).val * θ := hrep (h θ) θ hθ (by rw [← map_pow, hhm])
  have hadd : ∀ i j : ZMod m, zt X m ^ i.val * zt X m ^ j.val = zt X m ^ (i + j).val := by
    intro i j
    rw [← pow_add, ZMod.val_add, ← pow_eq_pow_mod _ hpow]
  have hhg : h (g θ) = zt X m ^ (ka X m θ h).val * g θ := by
    rw [hgθ, map_mul, map_pow, hhz, hhθ]
    ring
  refine ⟨?_, ?_, ?_⟩
  · refine hlg _ _ _ hθ ?_
    show g (h θ) = _
    rw [hhθ, map_mul, map_pow, hgz, hgθ, ← mul_assoc, hadd, add_comm]
  · exact hlg _ _ _ ((map_ne_zero g).2 hθ) hhg
  · refine hlg _ _ _ hθ ?_
    show g.symm (h (g θ)) = _
    have e2 : g.symm (zt X m) = zt X m := by
      rw [RingEquiv.symm_apply_eq, hgz]
    rw [hhg, map_mul, map_pow, e2, RingEquiv.symm_apply_apply]

end UpperTheory.V.Z.Kato.Sym.PE
