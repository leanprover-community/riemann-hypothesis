module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.AdaptedStandardBasis
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CovGmin

def Hyp (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o Lb : ℝ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    Prop :=
  LawsJ T ∧ 1 ≤ (T.Q.Dw j).p ∧ 1 ≤ (T.Q.Dw j).q ∧ 2 < Module.finrank ℚ D.host.E / 2 ∧ InR D j ∧ Y.Good e o ∧
    1 ≤ Lb ∧ Real.log Y.d.l₂.M ≤ 30 * Lb ∧ fieldSz D.host.E ≤ 3 * Lb ∧ Real.log (D.R.f * D.R.r) ≤ Lb ∧
    o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 ∧ Dom a n ∧ Even n ∧ 8 * D.R.f * D.R.r + 4 ≤ n ∧
    (∀ (τ : Psi T.Q.H) (k : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (k : ℕ) < (T.Q.Dw j).p →
      ((n / 2 : ℕ) : ℤ) < laOf (T.Q.Dw j) a n τ k) ∧
    Real.log (sizeK (T.Q.Dw j) a n) ≤ 20 * Lb

def badC {D : D7} {T : Core D} {j : ℕ} (Y : Deep T j) : ℕ := D.host.QS * D.host.q * D.host.d * Y.d.l₂.M

def thFam {D : D7} {T : Core D} {j : ℕ} (Y : Deep T j) (nab : NabV Y.d.Xo₂ Y.d.c₂) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (n : ℕ) (ρ : ℝ) : Set (Y.V (wtZ a n)) :=
  {y | ∃ (x0 : Fin n → LevQc (T.Q.Dw j) Y.d.l₂) (La : GenLat D.host.E n) (N : ℕ)
      (P : MvPolynomial (LtN (T.Q.Dw j) n) Y.d.c₂.F),
    Submodule.span (𝓞 D.host.E) (Set.range x0) = ⊤ ∧ La.Unimod ∧ La.TrivAt (badC Y) ∧ La.TrivAt Y.d.l₂.M ∧
      La.LevOK N Y.d.l₂.M ∧ P ∈ harmL Y.d.c₂ La a ∧ GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightData.polyNorm Y.d.c₂ P ≤ ρ ∧
      ∀ (p : TRing Y.d.c₂.F) (y' : FrPt Y.d.Xo₂ Y.d.c₂ p.R),
        thLaValAt Y.d.Xo₂ Y.d.c₂ nab (phiHat Y.d.c₂ (indPhi Y.d.c₂ x0)) La N P y' ((y : Rul Y.d.Xo₂ Y.d.c₂) p y')}

end GlobalTheory.CovGmin
