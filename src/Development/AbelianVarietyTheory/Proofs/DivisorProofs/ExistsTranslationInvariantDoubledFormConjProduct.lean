module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagFormBoxStarNeZero
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.DblDiagForm

open MeasureTheory GlobalTheory.DiagForm

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField

local instance measAfD {F : Type} [Field F] [NumberField F] : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
local instance borelAfD {F : Type} [Field F] [NumberField F] : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩

theorem lDiag_translate {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {φ : (κ ⊕ κ → AF F) → ℂ} (hφ : φ ∈ schA F (κ ⊕ κ)) (φ' : (κ ⊕ κ → AF F) → ℂ) (x : κ → AF F)
    (h : ∀ u, φ' (Sum.elim u u) = φ (Sum.elim (u + x) (u + x))) : lDiag F κ φ' = lDiag F κ φ := by
  have hi := integrable_resD hφ
  have e : resD F κ φ' = fun p => resD F κ φ (p + shiftOf x) := by
    funext p
    show φ' (Sum.elim (glue p) (glue p)) = φ (Sum.elim (glue (p + shiftOf x)) (glue (p + shiftOf x)))
    rw [h, glue_add_shiftOf]
  rw [lDiag, LinearMap.comp_apply, LinearMap.comp_apply, e,
    Lext_apply _ (hi.comp_add_right (shiftOf x)), Lext_apply _ hi]
  exact integral_add_right_eq_self _ _

theorem exists_form : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ Ψ ∈ schA F κ, Ψ ≠ 0 →
    ∃ l ∈ (adeleClass F).adm (κ ⊕ κ), (∀ φ ∈ schA F (κ ⊕ κ), ∀ (φ' : (κ ⊕ κ → AF F) → ℂ) (x : κ → AF F),
      (∀ u, φ' (Sum.elim u u) = φ (Sum.elim (u + x) (u + x))) → l φ' = l φ) ∧ l (GlobalTheory.InertDbl.dblFun Ψ) ≠ 0 := by
  intro F _ _ κ _ Ψ hΨ hne
  exact ⟨lDiag F κ, lDiag_adm, fun φ hφ φ' x h => lDiag_translate hφ φ' x h,
    GlobalTheory.DiagSq.lDiag_boxFun_star_ne F κ Ψ hΨ hne⟩

end GlobalTheory.DblDiagForm
