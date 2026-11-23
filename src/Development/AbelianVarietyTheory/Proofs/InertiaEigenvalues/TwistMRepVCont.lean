module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

namespace GlobalTheory.UseLoc
theorem twistM_repV_cont : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ), (Continuous fun g => M g) → Continuous (fun g => ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ g : (↥C.LL.1)ˣ) : ↥C.LL.1)) → ∀ x, Continuous fun g => repV C (twistM (locOC C M) θ) g x := by
  intro D i w hw C k M θ hM hθ x
  have hinc : Continuous fun y : ↥(OL (D.nbr i w hw).LL) => ((incO C.le y : ↥(OL C.LL)) : ↥C.LL.1) := by
    have e : (fun y : ↥(OL (D.nbr i w hw).LL) => ((incO C.le y : ↥(OL C.LL)) : ↥C.LL.1)) =
        fun y => IntermediateField.inclusion C.le y.1 := rfl
    rw [e]
    exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hmat : Continuous fun g => mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (twistM (locOC C M) θ) g := by
    refine continuous_matrix fun a b => ?_
    have h1 : Continuous fun g : Br.G D.nbr i w hw =>
        M ((decS D.nd w) ((Br.ι (D.nbr i w hw)) g)) a b :=
      (hM.matrix_elem a b).comp (continuous_subtype_val.comp (Br.ι_cont (D.nbr i w hw)))
    have h2 := hinc.comp ((D.nbr i w hw).eO_cont.comp h1)
    have e : (fun g => mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (twistM (locOC C M) θ) g a b) =
        fun g => ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ g : (↥C.LL.1)ˣ) : ↥C.LL.1) *
          ((incO C.le ((D.nbr i w hw).eO (M ((decS D.nd w) ((Br.ι (D.nbr i w hw)) g)) a b)) : ↥(OL C.LL)) : ↥C.LL.1) := by
      funext g
      simp [mapM, twistM, locOC, Br.locO, tableLineDegreeTwo.charL, Matrix.smul_apply]
    rw [e]
    exact hθ.mul h2
  have e2 : (fun g => repV C (twistM (locOC C M) θ) g x) =
      fun g => (mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (twistM (locOC C M) θ) g).mulVec x := by
    funext g
    rfl
  rw [e2]
  exact hmat.matrix_mulVec continuous_const
end GlobalTheory.UseLoc
