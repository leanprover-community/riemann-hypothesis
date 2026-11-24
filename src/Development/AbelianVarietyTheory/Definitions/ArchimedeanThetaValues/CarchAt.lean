module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
public import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementC
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

namespace GlobalTheory.ArcCM

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM

variable {D : D7}

def nAt (D : D7) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) : ℕ :=
  nQ D.host.E D.R.r (D.host.g 0 * D.host.g 1) (discr D.host.E).natAbs (Ideal.absNorm D.host.ccK)
    (WeightFamilies.c1 D CR Tt cc j) (ka.size + D.R.r)

def LaAt (D : D7) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) : ℝ :=
  LaQ D.host.E D.R.r (D.R.sigW j).2 (D.host.g 0 * D.host.g 1) (discr D.host.E).natAbs (Ideal.absNorm D.host.ccK)
    (WeightFamilies.c1 D CR Tt cc j) (ka.size + D.R.r)

def FamQ (T : Core D) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) (K₁ : Type) [Field K₁] [NumberField K₁]
    [Algebra T.Q.c.F K₁] (d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁) : Prop :=
  Fam (nAt D j ka CR Tt cc) (LaAt D j ka CR Tt cc) (WeightFamilies.c1 D CR Tt cc j) d

def KillQ {T : Core D} (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) : Prop :=
  ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁] (d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁),
    FamQ T j ka CR Tt cc K₁ d →
      ∀ F : (recB h).Cusp j ka, F ∈ WeightFamilies.MggK (recB h) CR Tt cc j ka → cfOf d.yF d.μ d.jj F.1 = 0

def DetectQ {T : Core D} (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) : Prop :=
  ∀ F : (recB h).Cusp j ka,
    (∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁] (d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁),
      FamQ T j ka CR Tt cc K₁ d → cfOf d.yF d.μ d.jj F.1 = 0) → F ∈ WeightFamilies.MggK (recB h) CR Tt cc j ka

def CarchAt (D : D7) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) : ℝ :=
  4 * Real.pi + archP D.host.E D.R.r (LaAt D j ka CR Tt cc) (WeightFamilies.c1 D CR Tt cc j) * ka.size

def BdegAt (large₂ : SizeData₂ D) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) : ℝ :=
  (pDeg large₂.logOm + (1 / 2) * Real.log (LaAt D j ka CR Tt cc)) * ka.size

def RoomAt (large₂ : SizeData₂ D) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc C A : ℝ) : Prop :=
  CarchAt D j ka CR Tt cc ≤ WeightFamilies.PPv D large₂ C A * ka.size ∧ BdegAt large₂ j ka CR Tt cc ≤ WeightFamilies.PPv D large₂ C A * ka.size ∧
    Real.log |((discr D.host.E : ℤ) : ℝ)| + Real.log (nAt D j ka CR Tt cc) ≤ WeightFamilies.PPv D large₂ C A

end GlobalTheory.ArcCM
