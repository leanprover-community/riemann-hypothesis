module

import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.WhittakerModels.UnipBEqUnipotent
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import GroundTheory.AutomorphicForms.SmoothRep
public import GroundTheory.AutomorphicForms.WhittakerGroups
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
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

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace PositivityTheory.rg.gu.whit

theorem unipB_eq_unipotent (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) : unipB k (Fin n) = GroundTheory.Automorphic.Iwasawa.unipotent k n := by
  ext g
  rw [mem_unipB]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j hij => h1 i j hij, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j hij => h1 hij, h2⟩

theorem whitChar_eq_psiN (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n : ℕ) (u : unipB k (Fin n)) :
    ((whitChar ψ n u : ℂˣ) : ℂ) =
      GroundTheory.Automorphic.Whittaker.psiN (Circle.coeHom.compAddChar ψ) (u : GL (Fin n) k) := by
  have hs : (∑ p : Fin n × Fin n with (p.2 : ℕ) = p.1 + 1, (u : GL (Fin n) k).val p.1 p.2) =
      GroundTheory.Automorphic.Whittaker.superdiagSum ((u : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    rfl
  show ((Circle.toUnits (ψ _) : ℂˣ) : ℂ) = ((ψ (GroundTheory.Automorphic.Whittaker.superdiagSum _) : Circle) : ℂ)
  rw [hs]
  rfl

theorem isAdmissible_iff {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) : GlobalTheory.PRep.IsAdmissible ρ ↔ GroundTheory.Automorphic.IsAdmissible ρ := by
  apply CompanionTheory.rg.gu.whit.isAdmissible_iff

end PositivityTheory.rg.gu.whit
