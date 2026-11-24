module

public import Formalism.AdmissibleDesigns.FiniteClassesContinuousLattice
public import Formalism.AdmissibleDesigns.KernelLengthHigherColumns
public import Formalism.AdmissibleDesigns.RankReductionIdempotentOne
public import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
public import Formalism.AdmissibleDesigns.ColumnUnramifiedCharacter
import Formalism.AdmissibleDesigns.EKSymmCont
public import Formalism.AdmissibleDesigns.IsDROfWpIso
public import Formalism.AdmissibleDesigns.MemIntegralSpanIffImage
import Formalism.AdmissibleDesigns.TheoremN5OfNormalizedItems
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Formalism.AdmissibleDesigns.CohomZeroEquivContinuous
import Formalism.AdmissibleDesigns.PiEquiv2

@[expose] public section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.StA

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF Formalism.MainNotions.N.K.St

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

section Cols2

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]




theorem colLx
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (hBK : TruncatedSeriesCountingIdentities.admBK i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (hFont : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i)
    (hDec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (hFin : LargeLevelLemmas.tateH1FinitenessAtPlacesOver i) :
    ∀ x' : Dd.X', Dd.p x' ∉ (D.nd.Z i : Set (D.nd.X i)) → ∀ l : Col i dc,
      ∃ Lx : Submodule (FractionRing (D.nd.O i))
          ((decs D.host.E (Aw i dc)) (colIdx i dc l) → EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x'),
        LinearMap.range (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
          ((decs D.host.E (Aw i dc)) (colIdx i dc l))) ≤ Lx ∧
        (∀ (f : LeftId (D.nd.O i) Dd.e₁ →ₗ[Dd.R'] EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')
          (z : coZ1s (resRep (uRep (D.nd.O i) (M := LeftId (D.nd.O i) Dd.e₁) Dd.r Dd.χ)
            ((decs D.host.E (Aw i dc)) (colIdx i dc l)))),
          Submodule.mkQ _ z ∈ KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.e₁) l →
          (fun g : (decs D.host.E (Aw i dc)) (colIdx i dc l) =>
            f ((z : (decs D.host.E (Aw i dc)) (colIdx i dc l) → LeftId (D.nd.O i) Dd.e₁) g)) ∈ Lx) ∧
        (∀ (f : LeftId (D.nd.O i) Dd.E →ₗ[Dd.R'] EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')
          (z : coZ1s (resRep (uRep (D.nd.O i) (M := LeftId (D.nd.O i) Dd.E) Dd.r Dd.χ)
            ((decs D.host.E (Aw i dc)) (colIdx i dc l)))),
          Submodule.mkQ _ z ∈ KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.E) l →
          (fun g : (decs D.host.E (Aw i dc)) (colIdx i dc l) =>
            f ((z : (decs D.host.E (Aw i dc)) (colIdx i dc l) → LeftId (D.nd.O i) Dd.E) g)) ∈ Lx) ∧
        Module.rank (FractionRing (D.nd.O i))
            (Lx ⧸ (LinearMap.range
              (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
                ((decs D.host.E (Aw i dc)) (colIdx i dc l)))).comap Lx.subtype) ≤
          (jN i ρ π dc (colIdx i dc l) + Module.finrank (FractionRing (D.nd.O i))
            (LinearMap.ker
              (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
                ((decs D.host.E (Aw i dc)) (colIdx i dc l)))) : ℕ) := by
  have hρ := K.Norm.rhoCont_of i r ρ π hDec hc
  refine colLx_of_ringDef i r ρ π dc g0 eB e₁ s Dd hD hc hBK hG2 hFont hDec
    (fun x' l => K.Font.crysX_of (i := i) (dc := dc) (r := r) (π := π) (g0 := g0) (eB := eB) (e₁ := e₁) (s := s)
      (Dd := Dd) ρ hG2 hD x' l)
    (fun x' l => K.Font.negX_of (i := i) (dc := dc) (r := r) (ρ := ρ) (π := π) (g0 := g0) (eB := eB) (e₁ := e₁)
      (s := s) (Dd := Dd) hFont hG2 hDec hc hρ hD x' l)
    (fun x' l => KTate.finX (i := i) (dc := dc) (r := Dd.r) (χ := Dd.χ) hFin x' l
      (KDim.contX_of_orbC i dc Dd.r Dd.χ x' l (KOrb.orbC_repE i dc r π g0 eB e₁ s Dd hD hc x' (colIdx i dc l))))
    (fun l => K.Font.crysW_of (i := i) (dc := dc) (r := r) (ρ := ρ) (π := π) hFont hG2 hDec hc hρ l)

end Cols2

end Formalism.MainNotions.N.K.StA

end
