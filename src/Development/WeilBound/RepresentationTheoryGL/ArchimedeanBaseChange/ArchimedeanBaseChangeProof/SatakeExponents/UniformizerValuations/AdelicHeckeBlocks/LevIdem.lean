module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LevIdem
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.IsCompactSub
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.RStabApply
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical



namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelH

theorem levIdem (h3 : Slots) : LevIdem := by
  intro E _ _ _ n S d a ha hS hd hPS
  obtain ⟨⟨G₁, eG₁⟩, ⟨G₂, eG₂⟩, ⟨o₁, c₁⟩, ⟨o₂, c₂⟩, hpi, hν⟩ := Lev6.main d hintProd h3 a ha hS hd hPS
  have eL : levSet S d a = Lev6.lvS d S a := Set.ext fun h => (Lev6.mem_lvS d S a h).symm
  have e₁ : lev₁ S d a = G₁ := by
    have : lev₁ S d a = Subgroup.closure (G₁ : Set (GL (Fin a) (Af E))) := by rw [eG₁, ← eL]; rfl
    rw [this, Subgroup.closure_eq]
  have e₂ : lev₂ S d a = G₂ := by
    have : lev₂ S d a = Subgroup.closure (G₂ : Set (GL (Fin (n - a)) (Af E))) := by rw [eG₂, ← eL]; rfl
    rw [this, Subgroup.closure_eq]
  have eP : ((G₁.prod G₂ : Subgroup (Hf E a (n - a))) : Set (Hf E a (n - a))) = Lev6.lvS d S a := by
    ext ⟨g, h⟩
    show g ∈ (G₁ : Set (GL (Fin a) (Af E))) ∧ h ∈ (G₂ : Set (GL (Fin (n - a)) (Af E))) ↔ _
    rw [eG₁, eG₂]
    exact (hpi g h).symm
  have hm : ∀ h : Hf E a (n - a), h ∈ G₁.prod G₂ ↔ h ∈ Lev6.lvS d S a := fun h => by
    rw [← SetLike.mem_coe, eP]
  rw [e₁, e₂, eP, eL]
  refine ⟨⟨by rw [eG₁]; exact o₁, by rw [eG₁]; exact c₁⟩, ⟨by rw [eG₂]; exact o₂, by rw [eG₂]; exact c₂⟩, rfl,
    fun ν hνH => ?_⟩
  obtain ⟨hne, hf⟩ := hν ν hνH
  refine ⟨((ν.real (Lev6.lvS d S a) : ℝ) : ℂ)⁻¹, inv_mul_cancel₀ hne, fun x y h => ?_⟩
  rw [hf x y h]
  by_cases hc : x = y ∧ h ∈ Lev6.lvS d S a
  · rw [if_pos hc, if_pos ⟨hc.1, (hm h).2 hc.2⟩]
  · rw [if_neg hc, if_neg (fun h' => hc ⟨h'.1, (hm h).1 h'.2⟩)]

end PositivityTheory.Rg.BcB.F

end
