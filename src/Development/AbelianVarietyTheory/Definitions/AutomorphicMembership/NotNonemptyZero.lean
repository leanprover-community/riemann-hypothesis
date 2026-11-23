module

public import Formalism.LocalToGlobal.UnitaryNorms.CharHost
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdeleSndSelf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqOfMapEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfCharOfCharOfHasInfQ

@[expose] public section

noncomputable section

namespace GlobalTheory.HeightCounting.CGTrueModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.CuspRep NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Char

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [_root_.NumberField.IsTotallyComplex E]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

end Char

section Eta

variable {R : Ranks} {H : Formalism.BasicNotions.Host R} {χ : HChar H.E}

theorem ordF_unif {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : ordF v (unif v) = 1 := by
  have h := unif_spec v
  have hk : Valued.v ((atFin v (Formalism.L2.Host.unif v) : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      v.valuation F (Formalism.L2.Host.unif v : F) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (Formalism.L2.Host.unif v : F)
  unfold IsUnifAt at h
  rw [ordF, ← hk, h, WithZero.log_exp]; simp

theorem prod_val (h : IsEtaT H χ) (v : HeightOneSpectrum (𝓞 H.F)) :
    ∏ P ∈ aboveF (L := H.E) H.F v, χ.val P = if (aboveF (L := H.E) H.F v).card = 1 then -1 else 1 := by
  obtain ⟨c, hc, hcm, hr, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have h1 := h.res.1 v (unif v)
  rw [etaFin, ordF_unif, zpow_one, HChar.resFin, MonoidHom.finsetProd_apply] at h1
  rw [← h1]
  refine Finset.prod_congr rfl fun P hP => ?_
  have hP' : P.under (𝓞 H.F) = v := by simpa [aboveF] using hP
  rw [MonoidHom.comp_apply, GlobalTheory.HeckeProduct.locK_unr χ (h.unr P), hr, hP', ordF_unif, zpow_one]

open Classical in
theorem above_eq {w w' : PlE H} (hc : IsConjPl H w w') : aboveF (L := H.E) H.F (w.under (𝓞 H.F)) = {w, w'} := by
  obtain ⟨c, hc', hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have h1 : GlobalTheory.Mem.Chr.ConjPl c.toRingEquiv w w' :=
    (GlobalTheory.Mem.Chr.conjPl_iff_mem _ _ _).2 fun x y e => hc x y (e.trans (hc' _))
  ext P
  have : P ∈ aboveF (L := H.E) H.F (w.under (𝓞 H.F)) ↔ P.under (𝓞 H.F) = w.under (𝓞 H.F) := by simp [aboveF]
  rw [this, GlobalTheory.Mem.Chr.under_eq_iff_conjPl c hcm.rank hcm.ne w P, Finset.mem_insert, Finset.mem_singleton]
  refine or_congr Iff.rfl ⟨fun h' => (GlobalTheory.Mem.Chr.existsUnique_conjPl _ w).unique h' h1, ?_⟩
  rintro rfl
  exact h1

theorem val_inert (h : IsEtaT H χ) {w : PlE H} (hw : ¬ IsSplitPl H w) : χ.val w = -1 := by
  have e : aboveF (L := H.E) H.F (w.under (𝓞 H.F)) = {w} := by
    ext P
    have : P ∈ aboveF (L := H.E) H.F (w.under (𝓞 H.F)) ↔ P.under (𝓞 H.F) = w.under (𝓞 H.F) := by simp [aboveF]
    rw [this, Finset.mem_singleton]
    refine ⟨fun h' => ?_, fun h' => h' ▸ rfl⟩
    by_contra hne
    exact hw ((GlobalTheory.Mem.GoodPlace.isSplitPl_iff H w).2 ⟨P, fun h => hne h.symm, h'⟩)
  have := prod_val h (w.under (𝓞 H.F))
  rw [e] at this
  simpa using this

theorem val_split (h : IsEtaT H χ) {w w' : PlE H} (hw : IsSplitPl H w) (hc : IsConjPl H w w') :
    χ.val w * χ.val w' = 1 := by
  apply _root_.GlobalTheory.HeightCounting.TrueSide.val_split <;> assumption

end Eta

end GlobalTheory.HeightCounting.CGTrueModel

end
