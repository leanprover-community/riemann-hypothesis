module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstOneMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBlochKatoReadOfTensorSelmerAddCoboundary
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
theorem _root_.GlobalTheory.T.isBlochKato_read_of_tensor_selmer_add_coboundary : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)) {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL))
    (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (a : ℕ) (z' : Br.G D.nbr i w hw → ↥(latC C (twistM N θ)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.InHfX (Br.PD D.loc D.nbr i w hw) (latC C (twistM N θ)) (latC C N) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' →
    (fun g => iotaW ↥C.LL.1 lam a k (z' g)) ∈ HfD (Br.PD D.loc D.nbr i w hw) (latC C N) := by
  first | exact @GlobalTheory.UseLoc.Cases.readW_main | exact GlobalTheory.UseLoc.Cases.readW_main | (intros; apply GlobalTheory.UseLoc.Cases.readW_main <;> assumption)
