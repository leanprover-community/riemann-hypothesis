module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UValThruTopOfDisjoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalZRam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointClosureEqOfIsClopen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafDescendingDivisorPowerStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUSetupProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryExistsNormalModelEffCartierAlongTraitsStatement
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem _root_.GlobalTheory.UPoinc.exists_uSetup_ideal_over_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (A : Set C.Z), IsClopen A → IsIrreducible A → (A ∩ Set.range C.i).Nonempty → ∃ (X₁ : USetup C) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι ∧ Set.range X₁.π = A ∧ (∀ x ∈ J₁.support, X₁.π x ∉ Set.range C.i) ∧ UValThru Xo c C.i X₁.π Set.univ φ J₁ ι := by
  intro E _ _ _ H Dw hpq φ hφ l Xo c C A hAc hAi hAm
  obtain ⟨η, hη, hcl⟩ := GlobalTheory.UPoinc.exists_genericPoint_closure_eq_of_isClopen E H Dw hpq l Xo c C A hAc hAi hAm
  obtain ⟨X₁, -, hpr, hX₁⟩ := GlobalTheory.UPoinc.GSetup.exists_uSetup_proj E H Dw hpq l Xo c C η hη 0
  have hr := GlobalTheory.UPoinc.USetup.range_π_eq E H Dw hpq l Xo c C X₁ η A hX₁ hcl
  obtain ⟨ι, Y, πY, D, hι, hhom, hprop, hnY, hsupp, hord⟩ := GlobalTheory.T.unitary_exists_normalModel_effCartier_along_traits E H Dw hpq φ hφ l Xo c C X₁ hpr
  obtain ⟨ι', J₁, hι', hsupp', hord'⟩ := GlobalTheory.T.exists_idealSheaf_descending_divisor_power E H Dw hpq φ hφ l Xo c C X₁ ι Y πY D hι hhom hprop hnY hsupp hord
  obtain ⟨hs, ho⟩ := GlobalTheory.UPoinc.ideal_orders_of_proper_model E H Dw hpq φ hφ l Xo c C X₁ Y πY hhom hprop ι' J₁ hsupp' hord'
  exact ⟨X₁, ι', J₁, hι', hr, hs, ho⟩
