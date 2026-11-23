module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCsdOfCharOfRes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApplyIdeleMapInfIdeleNegOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterThetaInvariantExponent
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

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.SplitChar

theorem locK_mul_locK_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ w u : Pl E, u ≠ w → u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → ∀ k : Eˣ, μ.locK u k * μ.locK w (Units.map (MonoidHomClass.toMonoidHom (IsCMField.complexConj E)) k) = 1 := by
  intro E _ _ _ μ e h w u hne hunder k
  have hc : GlobalTheory.Mem.Chr.ConjPl (IsCMField.complexConj E).toRingEquiv u w := by
    have hw : w ∈ aboveF (L := E) (maximalRealSubfield E) (u.under (𝓞 (maximalRealSubfield E))) := by
      simp [aboveF, hunder]
    exact ((GlobalTheory.CuspRep.NormTriv.mem_aboveF_iff u w).1 hw).resolve_left (Ne.symm hne)
  have h1 := GlobalTheory.CuspRep.NormTriv.normFin_loc _ μ hc k
  refine (Eq.trans ?_ h1.symm).trans ?_
  · rfl
  · rw [GlobalTheory.CuspRep.NormTriv.normFin, MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply,
      MonoidHom.mul_apply, MonoidHom.id_apply, map_mul, GlobalTheory.BCT.MuProps.finId_conjFin, ← GlobalTheory.PolChar.ideleConj_eq]
    rw [map_mul]
    exact GlobalTheory.BCT.MuProps.mu_mul_conj h _

end GlobalTheory.BCT.SplitChar
