module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.HasTypeVecIff
public import GroundTheory.LocalFields.UnramifiedHensel
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.LocHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.TameSuppUniqueHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.UnlLoc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredityGenericProduct
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.Outright
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.Gal.TypesAndIwahori

theorem unlinked_of_typeVec (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (N c : ℕ) (d : Fin c → ℕ) (hd : ∑ b, d b = N) (hpos : ∀ b, 0 < d b) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible) (hg : IsGeneric π)
    (θ : Fin c → 𝓀[k]ˣ →* ℂˣ) (hθ : Function.Injective θ) (hv : HasTypeVec π (stdBlocks d hd) θ)
    (s : Multiset (IrrGL (k := k))) (hS : HasSupport π s) : GlobalTheory.RoadU.Unlinked s :=
  unlinked_of_tameSphProd loc_holds GlobalTheory.RgGu.Holds.genericUnlinkedGL_holds PositivityTheory.Exh.langlandsMultisegments_holds
    PositivityTheory.Exh.standardCosocleGL_holds
    (GlobalTheory.CompanionTheory.Leib.genericProdIff_of_whitHeredity _ (GlobalTheory.CompanionTheory.Rodier.whitHeredity _)) hg hθ
    (topB_holds k N c d hd hpos V π hs hi θ hθ hv) hS

end UpperTheory.Gal.TypesAndIwahori
