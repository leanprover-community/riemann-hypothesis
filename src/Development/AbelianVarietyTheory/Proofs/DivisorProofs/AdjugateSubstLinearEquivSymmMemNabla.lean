module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSmulMemOfLeLocP
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.TauLatticeLatticeHolds
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem funEquiv_symm_mem_nabAt_of_nabAtr : ∀ {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Fintype ι]
    (emb : ι → E →+* K) {n : ℕ} (σ : ι → DomWeight n) (M : Submodule (𝓞 E) (Fin n → E)),
    Submodule.IsLattice E M → ∀ (v : VV K fun τ => (σ τ).dual),
    v ∈ nabAtr emb (fun τ => (σ τ).dual) M → (GlobalTheory.FunObj.funEquiv σ).symm v ∈ nabAt emb σ M := by
  intro E K ι _ _ _ _ _ emb n σ M hM v hv
  have hA : ∀ τ, (tauLat emb τ M).FG := by
    classical
    intro τ
    obtain ⟨S, hS⟩ := hM.fg
    rw [Formalism.L2.DIV.du_tauLat_eq, ← hS, Formalism.L2.DIV.du_tl_span]
    exact ⟨S.image (Formalism.L2.DIV.du_f (emb τ)), by rw [Finset.coe_image]⟩
  change ((GlobalTheory.FunObj.funEquiv σ).symm v).1 ∈ nabP σ (fun τ => tauLat emb τ M)
  simp only [nabP, transLat, Submodule.mem_iInf, Submodule.mem_comap]
  intro w B hB
  have hB' : ∀ τ, IsBasisAt w (dualFr (tauLat emb τ M)) (invTrK B τ) := fun τ =>
    GlobalTheory.DualWeylDual.isBasisAt_dualFr w (hA τ) (hB τ)
  have h1 : v.1 ∈ nabP (fun τ => (σ τ).dual) (fun τ => dualFr (tauLat emb τ M)) := hv
  simp only [nabP, transLat, Submodule.mem_iInf, Submodule.mem_comap] at h1
  have h2 := h1 w (invTrK B) hB'
  rw [← map_inv] at h2
  obtain ⟨s, hs, hsv⟩ := (Formalism.L2.DIV.lc_mem_locP w _ _).1 h2
  refine (Formalism.L2.DIV.lc_mem_locP w _ _).2 ⟨s, hs, ?_⟩
  set F := (GlobalTheory.FunObj.funEquiv σ).symm v with hF
  have e2 : GlobalTheory.FunObj.funEquiv σ (s • rhoK σ B⁻¹ F) = s • rhoK (fun τ => (σ τ).dual) (invTrK B⁻¹) v := by
    rw [LinearMapClass.map_smul_of_tower, GlobalTheory.FunObj.funEquiv_rhoK, hF, LinearEquiv.apply_symm_apply]
  have h3 : (s • rhoK σ B⁻¹ F).1 ∈ nabStd K σ := by
    rw [GlobalTheory.FunObj.funEquiv_mem_nabStd, e2]
    exact hsv
  exact h3

end GlobalTheory
