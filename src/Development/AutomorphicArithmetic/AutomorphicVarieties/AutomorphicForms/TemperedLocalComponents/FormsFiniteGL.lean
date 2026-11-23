module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.AutomorphicFormsLeSm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.OneTmulMemCenter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CoefficientSpans.FiniteCoeffSpan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFinite
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

theorem UpperTheory.V.Af.formsFiniteGL :
    GlobalTheory.Published.AutomorphicFormsFiniteGL := by
  refine CoefficientSpans.finite_of (CoefficientSpans.charFinite_of Fin.formsFinite) (fun E _ _ _ a φ h => (Cm.isAutForm_iff φ).1 h)
    (fun E _ _ _ a => ⟨(Cm.cptEq E a).symm, fun φ k g => ?_⟩)
    (fun E _ _ _ a z hz => ⟨Cm.uTC E a z, ?_, fun _ _ => rfl⟩)
  · obtain ⟨k, rfl⟩ := (Cm.cptEq E a).surjective k
    rw [MulEquiv.symm_apply_apply, Cm.infEmb_cptEq]
    rfl
  · have h := Cm.uTC_mem_Zalg hz
    rw [Cm.Zalg_eq_map, Cm.center_UC, AlgHom.map_adjoin] at h
    refine Algebra.adjoin_mono ?_ h
    rintro _ ⟨_, ⟨τ, u, rfl⟩, rfl⟩
    exact ⟨τ, u, Cm.uC_capC τ u⟩
