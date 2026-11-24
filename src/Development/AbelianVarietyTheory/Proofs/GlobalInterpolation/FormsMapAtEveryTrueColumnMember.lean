module

public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ChiLastStepFiniteOrderSymTie
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPrimitiveRootsCoeffFieldTrueColumns
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FormsMapOfSymmetricComparisonLowerMapFiniteChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BranchingNormIdentityTrueColumnsMembers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStandardColumnComparisonsTrueColumns
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerMapTie
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

theorem formsMap_at_every_trueColumnMember : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (u : (I.rec7 l Z).what₂.Word), Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 (I.rec7 l Z) u := by
  intro B X I hOk hP l Z u
  obtain ⟨C, hC, -⟩ := GlobalTheory.Mem.Col2.TC.colsTiedSym_std I hOk hP l Z
  have hF := hC u
  have hL := GlobalTheory.Mem.Col2.LowerTie.lowerMap_tie I hOk hP l Z u _ _ (C.forms u) hF
  have hB := GlobalTheory.Mem.Col2.TC.beOnTie_true I hOk hP l Z u
  have hR : ∀ i, (∃ ζ : (I.rec7 l Z).what₂.LL, IsPrimitiveRoot ζ ((I.rec7 l Z).host.g i)) ∧
      ∃ ζ : (I.rec7 l Z).what₂.LL, IsPrimitiveRoot ζ ((I.rec7 l Z).host.g i - 1) :=
    fun i => GlobalTheory.trueCols_exists_primitiveRoots I hOk l Z i
  exact GlobalTheory.RedPt0.formsMap_of_symmetricComparison_lowerMap_finiteChar (I.rec7 l Z) u _ _ (C.forms u) hL hB
    (GlobalTheory.chi_last_step_finite_order_symTie (I.rec7 l Z) u _ _ (C.forms u) hR)

end GlobalTheory.Mem.Col2.TC
