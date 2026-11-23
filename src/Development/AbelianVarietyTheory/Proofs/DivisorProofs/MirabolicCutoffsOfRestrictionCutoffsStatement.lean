module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MirabolicCutoffsOfRestrictionCutoffs
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

@[expose] public section

open Matrix Topology

theorem _root_.GlobalTheory.T.mirabolic_cutoffs_of_restriction_cutoffs : ∀ {F : Type} [NormedField F] [ProperSpace F] [IsUltrametricDist F] (ψ : AddChar F ℂ), IsLocallyConstant ψ → ψ ≠ 1 → ∀ m : ℕ, (∀ B : Subgroup (GL (Fin (m + 1)) F), IsCompact (B : Set (GL (Fin (m + 1)) F)) → IsOpen (B : Set (GL (Fin (m + 1)) F)) → ∀ L : Set (Fin (m + 1) → F), L ∈ nhds (0 : Fin (m + 1) → F) → ∀ h₀ : GL (Fin (m + 1)) F, ∃ T : GL (Fin (m + 2)) F →₀ ℂ, ∀ f : GL (Fin (m + 2)) F → ℂ, GlobalTheory.JSW.KirFin.Eqv ψ f → (∀ b ∈ B, ∀ g, f (g * GlobalTheory.JSW.KirFin.cor b) = f g) → (∀ y ∈ L, ∀ g, f (g * GlobalTheory.JSW.KirFin.mir 1 y) = f g) → ∀ h : GL (Fin (m + 1)) F, GlobalTheory.JSW.Cut.act T f (GlobalTheory.JSW.KirFin.cor h) = (GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin (m + 1)) F))).indicator (fun h => f (GlobalTheory.JSW.KirFin.cor h)) h) → ∀ U : Subgroup (GL (Fin (m + 2)) F), IsCompact (U : Set (GL (Fin (m + 2)) F)) → IsOpen (U : Set (GL (Fin (m + 2)) F)) → ∀ z : GL (Fin (m + 2)) F, GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin (m + 2)) F)) (GlobalTheory.JSW.Cut.cell z (U : Set (GL (Fin (m + 2)) F))) {p | GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1} := by
  first | exact @GlobalTheory.JSW.Cut.cuts_mir_of_res | exact GlobalTheory.JSW.Cut.cuts_mir_of_res | (intros; apply GlobalTheory.JSW.Cut.cuts_mir_of_res <;> assumption)
