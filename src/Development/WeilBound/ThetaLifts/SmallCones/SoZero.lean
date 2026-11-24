module

public import Development.WeilBound.ThetaLifts.CTKernel
public import Development.WeilBound.ThetaLifts.SmallCones.SoDefs
public import Development.WeilBound.ThetaLifts.SmallCones.FormSwapZero
public import Development.WeilBound.ThetaLifts.SmallCones.KerPol
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.WeilBound.ThetaLifts.SmallCones.KerGeo

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKCT

open NumberField Matrix GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.ThK PositivityTheory.ThKG So Ker

theorem soZeroA'_of (hL : LinEx) (hX : MixX) (hE : ThetaExp) (hU : EvUniq) : SoZeroA' := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' hB hXh hW hM hM₀ M₁ hM₁
    ⟨χX, χW, om₁, om₀, r₁, s₁, r₀, s₀, r₂, s₂, hP₁, hP₀⟩ e₀ e he₀ he Ψ hΨ hso
  obtain ⟨eX, heX⟩ := (hX F E σ B n d₁ X W₁ M₁ χX χW om₁ r₁ s₁ r₂ s₂ hP₁ n₁ X₁ H j₀ j₁ M₀ om₀ r₀ s₀ hH hP₀).1
  have pg := pg_herm hB hH hXh
  have pg' := pg_skew hB hH' hW
  have hne := comp_ne (polX (W := W₁) pg (skew_det hP₁.skew)) hE hB hM hM₁ hM₀ he₀ heX
  have hc := isEv_comp (K := isoA H H') hB.std hM hM₁ hM₀ he₀ heX hne (by
    rintro u (h | ⟨z, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨_, ⟨z, rfl⟩, by rw [incM_one, Matrix.one_mul, vv_mul_r]⟩)
  rw [Matrix.one_mul, Matrix.mul_one] at hc
  obtain ⟨c, -, h⟩ := (polA pg pg').uniq hU hB hM hM₀ (isEv_sumA hB.std pg' hc) (isEv_sumA hB.std pg' he)
  rw [h Ψ hΨ, LinearMap.comp_apply, ev_zero hL hB hP₁.herm hP₁.skew hM₁ _ eX (x_ne hH) (fun z => heX.inv _ ⟨z, rfl⟩) _ hso, smul_zero]

end PositivityTheory.ThKCT

end
