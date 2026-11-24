module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.ArthurClozelDescent
import Formalism.LocalToGlobal.UnitaryNorms.CharTransport

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Topology Matrix Neutral.B1 Formalism.L2.Host Formalism.L2.Host.CT GlobalTheory.CuspRep
open scoped ContDiff

namespace UpperTheory.V.Lit

section Comp

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E]


omit [IsTotallyReal E] in
private def zf (y : Af E) : Ad E := ((0, y) : InfiniteAdeleRing E × Af E)


private theorem split (x : Ad E) : x = TR.sInf E (TR.pInf E x) + zf (pFin E x) :=
  Prod.ext (((TR.infEq E).apply_symm_apply _).symm.trans (add_zero _).symm) (zero_add _).symm


variable {σ : E ≃+* E} {s : Ad E →+* Ad E} (hs : IsAdExt (σ : E →+* E) s)
include hs

end Comp

section Pull

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ}



variable {σ : E ≃+* E} {s : Ad E →+* Ad E} (hs : IsAdExt (σ : E →+* E) s)
include hs


end Pull

end UpperTheory.V.Lit
