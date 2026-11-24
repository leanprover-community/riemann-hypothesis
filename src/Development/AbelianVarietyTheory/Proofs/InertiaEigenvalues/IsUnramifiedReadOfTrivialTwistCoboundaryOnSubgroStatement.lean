module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstOneMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedReadOfTrivialTwistCoboundaryOnSubgro
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore

@[expose] public section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnramified_read_of_trivialTwist_coboundary_on_subgroup : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (a : ℕ) (I : Subgroup (Br.G D.nbr i w hw))
    (z' : Br.G D.nbr i w hw → ↥(latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ 1)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.IsUnr (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ 1)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) I z' →
    (fun g => iotaC ↥C.LL.1 lam a (z' g)) ∈ Z1urD (latC C (locOC C (chiRatO D.nd i 1))) I := by
  first | exact @GlobalTheory.UseLoc.Cases.readU_unr | exact GlobalTheory.UseLoc.Cases.readU_unr | (intros; apply GlobalTheory.UseLoc.Cases.readU_unr <;> assumption)
