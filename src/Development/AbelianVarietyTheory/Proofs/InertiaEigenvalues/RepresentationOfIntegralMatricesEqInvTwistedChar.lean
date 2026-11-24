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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstOneMem

@[expose] public section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

namespace GlobalTheory.UseLoc.Cases

theorem chiOC_one {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) : chiOC C 1 = 1 := by
  ext g; simp [chiOC]

theorem chiT_one {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) : chiT C θ 1 = θ := by
  rw [chiT, mul_inv_cancel, chiOC_one, one_mul]

theorem repV_eq_inv_smul_twist : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (g : Br.G D.nbr i w hw),
    repV C N g = ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ 1) g)⁻¹ : (↥C.LL.1)ˣ).val • repV C (twistM N θ) g := by
  intro D i w hw C k N θ g
  rw [chiT_one]
  have h : repV C (twistM N θ) g = (algebraMap (↥(OL C.LL)) (↥C.LL.1) (θ g : ↥(OL C.LL))) • repV C N g := by
    simp only [repV, matRep, mapM, twistM]
    simp [RingHom.mapMatrix_apply, Matrix.map_smul', Matrix.toLinAlgEquiv'_apply]
    rw [show ((θ g : ↥(OL C.LL)) • N g).map (algebraMap ↥(OL C.LL) ↥C.LL.1)
        = (algebraMap ↥(OL C.LL) ↥C.LL.1 (θ g : ↥(OL C.LL))) • (N g).map (algebraMap ↥(OL C.LL) ↥C.LL.1) from by
          ext a b; simp [Matrix.map_apply], map_smul]
    rfl
  rw [h, smul_smul]
  simp [tableLineDegreeTwo.charL]

end GlobalTheory.UseLoc.Cases
