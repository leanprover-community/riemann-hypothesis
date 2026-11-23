module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AutomorphicArithmetic.PrimeDiscriminants.Scales

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopVal

theorem isJ_smul {D : D7} {u : D.what₂.Word} {S : D.what₂.Tau → SPar} {M : Formalism.IndefR.Mult.DSModel D.sp.X' S}
    {j : SmT M →ₗ[ℂ] (Formalism.L2.Forms.FrP D → ℂ)} (h : GlobalTheory.Core.Rk.Top.IsJ u M j) {a : ℂ} (ha : a ≠ 0) :
    GlobalTheory.Core.Rk.Top.IsJ u M (a • j) := by
  constructor
  · intro x y e
    exact h.inj (smul_right_injective (Formalism.L2.Forms.FrP D → ℂ) ha e)
  · exact (LinearMap.range_smul j a ha).trans h.range
  · intro τ g hg v w hw y y' hy
    exact congrArg (a * ·) (h.eqv τ g hg v w hw y y' hy)

theorem levG_one {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {Pm : PeriodMap D.R C}
    {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm} {bad} (K : Formalism.L2.Forms.ClassesAtPrimes M bad)
    {J : Set (GA D D.sp.X')} {χ : GA D D.sp.X' → ℂ} (h1 : ∀ g, g ∈ J ↔ ∃ κ : K.lev.U, GlobalTheory.Core.Rk.Top.HasMat g κ.1)
    (h2 : ∀ g (κ : K.lev.U), GlobalTheory.Core.Rk.Top.HasMat g κ.1 → χ g = star ((K.lev.chi κ : ℂˣ) : ℂ)) : LevG K 1 J χ := by
  simp only [LevG, inv_one, one_mul, mul_one]
  exact ⟨h1, h2⟩


end GlobalTheory.TopVal
