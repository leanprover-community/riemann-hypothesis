module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchesParahoricLevels
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
open GlobalTheory.CuspMult

theorem _root_.GlobalTheory.T.isometry_matches_parahoric_levels : ∀ {D : D7} (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (r t : ℕ) (hr : r ≤ V.rank) (hr' : r ≤ V'.rank) (Pg : Finset (Pl D.host.E)) (χ χ' : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)) (Φ : GfC V ≃ₜ* GfC V'), IsFinIso V V' β β' Pg j Φ → ∀ κ : GfC V, (finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) ↔ finE V' (Φ κ : GA D V') ∈ parLev D.sp.cm V'.gram β' (princDat V'.rank r t hr' Pg χ')) ∧ (finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) → (rTup β' (princDat V'.rank r t hr' Pg χ') (finE V' (Φ κ : GA D V')) : G0 Pg r) = (rTup β (princDat V.rank r t hr Pg χ) (finE V (κ : GA D V)) : G0 Pg r)) := by
  exact @GlobalTheory.LevTrans.levtrans
