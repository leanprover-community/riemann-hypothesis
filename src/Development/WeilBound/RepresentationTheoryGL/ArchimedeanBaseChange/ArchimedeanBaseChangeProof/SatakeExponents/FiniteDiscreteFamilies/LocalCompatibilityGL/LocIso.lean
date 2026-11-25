module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.FinDiscNOf
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.F.F5.Bo

namespace LocalIsomorphism

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem finRep_eq_act (h : GL (Fin N) (Af E)) (φ : Sm E N) : finRep E N h φ = act (.fin h) φ := by
  rfl

end LocalIsomorphism

theorem LocIso_holds : LocIso := by
  intro E _ _ _ N V V' hV w σ hσ
  obtain ⟨f, hf0, hfV, hfeq⟩ := hσ
  obtain ⟨T, hT⟩ := hV
  refine ⟨(Submodule.subtype V').comp ((T : V →ₗ[ℂ] V').comp (f.codRestrict V hfV)), ?_, ?_, ?_⟩
  · intro h0
    apply hf0
    refine LinearMap.ext fun v => ?_
    have h1 := LinearMap.congr_fun h0 v
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, Submodule.coe_subtype,
      ZeroMemClass.coe_eq_zero, LinearEquiv.coe_coe] at h1
    have h2 : f.codRestrict V hfV v = 0 := by
      simpa using (T.map_eq_zero_iff).1 h1
    simpa [LinearMap.codRestrict] using congrArg Subtype.val h2
  · intro v
    exact (T _).2
  · intro g v
    have key := hT (.fin (locGL E N w g)) (f.codRestrict V hfV v) (f.codRestrict V hfV (σ.ρ g v))
      (by simp only [LinearMap.codRestrict_apply]; rw [hfeq, LocalIsomorphism.finRep_eq_act])
    simp only [LinearMap.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe]
    rw [key, LocalIsomorphism.finRep_eq_act]

end PositivityTheory.Rg.BcB.F.F5.Bo

end
