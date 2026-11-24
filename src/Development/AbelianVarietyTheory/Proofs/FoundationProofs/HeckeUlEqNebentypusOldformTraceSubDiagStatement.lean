module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashToGLSmul
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUlEqNebentypusOldformTraceSubDiag
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.heckeUl_eq_nebentypus_oldformTrace_sub_diag : ∀ (N l : ℕ) (k : ℤ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) (χ : DirichletCharacter ℂ N) (B : ℍ → ℂ), 0 < l → ChiInv k N N χ B → UlF k l B = χ (l : ZMod N) • (trOld k N l a b h (B ∣[k] toGL (dg l 1)) - B ∣[k] toGL (dg l 1)) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.ulF_eq_trOld | exact GlobalTheory.HeckeFamilyMatrices.ulF_eq_trOld | (intros; apply GlobalTheory.HeckeFamilyMatrices.ulF_eq_trOld <;> assumption)
