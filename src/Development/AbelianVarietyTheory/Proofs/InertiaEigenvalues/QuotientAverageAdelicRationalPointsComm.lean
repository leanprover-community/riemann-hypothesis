module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageMapLatticeEquivStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageProdFubini
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageProdFubiniStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

section General

variable {G₁ G₂ : Type} [AddCommGroup G₁] [TopologicalSpace G₁] [AddCommGroup G₂] [TopologicalSpace G₂]

variable [IsTopologicalAddGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁]
  [IsTopologicalAddGroup G₂] [LocallyCompactSpace G₂] [SecondCountableTopology G₂] [T2Space G₂]

def swapEquiv (G₁ G₂ : Type) [AddCommGroup G₁] [TopologicalSpace G₁] [AddCommGroup G₂] [TopologicalSpace G₂] :
    (G₂ × G₁) ≃ₜ+ (G₁ × G₂) :=
  { AddEquiv.prodComm with
    continuous_toFun := continuous_swap
    continuous_invFun := continuous_swap }

theorem avg_comm_of_isCoLat {Γ₁ : AddSubgroup G₁} {Γ₂ : AddSubgroup G₂} (h₁ : IsCoLat Γ₁) (h₂ : IsCoLat Γ₂)
    (Φ : G₁ × G₂ → ℂ) (hΦ : Per (Γ₁.prod Γ₂) Φ) :
    avg Γ₁ (fun x => avg Γ₂ (fun y => Φ (x, y))) = avg Γ₂ (fun y => avg Γ₁ (fun x => Φ (x, y))) := by
  have hs : Per (Γ₂.prod Γ₁) (fun p : G₂ × G₁ => Φ (p.2, p.1)) := by
    refine ⟨hΦ.1.comp continuous_swap, fun γ hγ x => ?_⟩
    exact hΦ.2 (γ.2, γ.1) ⟨hγ.2, hγ.1⟩ (x.2, x.1)
  have a := GlobalTheory.T.quotientAverage_prod_fubini G₁ G₂ Γ₁ Γ₂ h₁ h₂ Φ hΦ
  have b := GlobalTheory.T.quotientAverage_prod_fubini G₂ G₁ Γ₂ Γ₁ h₂ h₁ _ hs
  have c := GlobalTheory.T.quotientAverage_map_lattice_equiv (G₂ × G₁) (G₁ × G₂) (Γ₂.prod Γ₁) (Γ₁.prod Γ₂) (isCoLat_prod h₂ h₁) (isCoLat_prod h₁ h₂) (swapEquiv G₁ G₂)
    (fun x => ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩) Φ hΦ
  exact a.symm.trans (c.symm.trans b)

end General

theorem avg_comm (E : Type) [Field E] [NumberField E] (ι κ : Type) [Fintype ι] [Fintype κ]
    (Φ : (ι → Ad E) × (κ → Ad E) → ℂ) (hΦ : Per ((ratV E ι).prod (ratV E κ)) Φ) :
    avg (ratV E ι) (fun x => avg (ratV E κ) (fun y => Φ (x, y))) =
      avg (ratV E κ) (fun y => avg (ratV E ι) (fun x => Φ (x, y))) :=
  avg_comm_of_isCoLat (isCoLat_ratV E ι) (isCoLat_ratV E κ) Φ hΦ

end GlobalTheory.CuspGeneric
