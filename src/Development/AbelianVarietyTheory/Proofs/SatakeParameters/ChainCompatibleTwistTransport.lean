module

public import Formalism.LocalToGlobal.Divisibility.Tuples
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ColumnAvoidanceConditions
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

noncomputable section

namespace GlobalTheory.ColPeriodCompare

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke

section Mem

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L]

def unramOff (S : Set ℕ) (v : HeightOneSpectrum (𝓞 F)) : Subgroup (Chr F E L) :=
  ⨅ _ : ¬ GoodPl E S v, kills Lˣ (inertAt E v)

def IsTwist (S : Set ℕ) (x : Chr F E L) : Prop :=
  x ∈ finChar F E L ⊓ kills Lˣ (idF F E).range ⊓ (⨅ v : HeightOneSpectrum (𝓞 F), kills Lˣ (wildAt E v)) ∧
    x ∈ ⨅ v : HeightOneSpectrum (𝓞 F), unramOff F E L S v

end Mem

section Transport

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S S' : Set ℕ}
  {χ : Chr X.F X.E X.K} (h : IsTwist X.F X.E X.K S χ) (h' : IsTwist X.F X.E X.K S' χ)
  (cst : LocCst X (uSG Pr.vGs (QE sel χ))) (L : ChIdx X Pr R (QE sel χ))

end Transport

section Chain

variable (D : D7) (EX : ErrX D) (Ch : Chars (ColumnAvoidanceConditions.fieldsOf D) (ColumnAvoidanceConditions.primesOf D EX) D.R.m)
  (m0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E)
  (sel : HeightOneSpectrum (𝓞 (ColumnAvoidanceConditions.fieldsOf D).F) → HeightOneSpectrum (𝓞 (ColumnAvoidanceConditions.fieldsOf D).E)) {S S' : Set ℕ}
  (A : Amb (ColumnAvoidanceConditions.fieldsOf D)) (u : D.what₂.Word) (μ : D.what₂.Tup)

end Chain

end GlobalTheory.ColPeriodCompare
