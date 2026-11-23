module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolyEqOfIsRowPar
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsReading
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section



section
noncomputable section
namespace GlobalTheory.EigTie
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.Triple (IsParam IsResidual FbAt)
open GlobalTheory.HeightCounting (RowSide PlSide IotaOk setTy factRes)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE OnW)
variable {D : D7}
theorem residual_ties_of_charpoly_reduction {Rw : RowSide D} {Pl : PlSide D} (h : IotaOk D Pl)
    (hr : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ σ π r, D.nd.goodRow σ → OnW D σ → IsRowPar Rw σ π →
      _root_.UpperTheory.GalS.IsGaloisRepOfN D π _ (Pl.ι w) r → IsSSRep (D.ntypes.rbar σ w) ∧ ∀ g, ∃ p : (Zbar (D.what₂.places.resChar w))[X],
        p.map (Zbar (D.what₂.places.resChar w)).subtype = ((r g : GL (Fin D.R.r) (Qbar (D.what₂.places.resChar w))) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.what₂.places.resChar w))).charpoly ∧
        p.map (plRed Pl w) =
          ((D.ntypes.rbar σ w g : GL (Fin D.R.r) (FbAt D w)) : Matrix (Fin D.R.r) (Fin D.R.r) (FbAt D w)).charpoly) :
    _root_.GlobalTheory.EigTie.ResTiedAlt D Rw := by
  intro w hw l _ e
  subst e
  exact ⟨Pl.ι w, plRed Pl w, Pl.ι_w w, teichAt_of_iotaOk h w, fun σ π r h1 h2 h3 h4 =>
    ⟨(hr w hw σ π r h1 h2 h3 h4).1, (hr w hw σ π r h1 h2 h3 h4).2, teichAt_of_iotaOk h w⟩⟩
end GlobalTheory.EigTie
end
end
