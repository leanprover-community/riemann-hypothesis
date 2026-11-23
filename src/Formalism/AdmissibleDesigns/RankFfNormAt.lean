module

public import Formalism.AdmissibleDesigns.MemIntegralSpanIffImage
public import Formalism.AdmissibleDesigns.KernelLengthHigherColumns
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Classical Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.NG

namespace Formalism.MainNotions.N.KTate

open Formalism.MainNotions.N.KHf

section RecIso2

open Formalism.MainNotions Formalism.MainNotions.N Formalism.RepresentationBoundsCohomology.SF NumberField IsDedekindDomain
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData)

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)



theorem isoV_of (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (g0 : GE D.nd)
    (eB e₁ s : D.nd.X i → MatN D.nd i)
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (l : K.Col i dc) : IsoV i dc Dd ρ π l := by
  have hn := KDim.col_over i dc l
  let F : TrV (eK (D.nbr i _ hn)) (KFin.Vr i Dd) ≃ₗ[Br.LL D.nbr i _ hn] (Fin D.R.r → Br.LL D.nbr i _ hn) :=
    { toFun := fun v a => eK (D.nbr i _ hn) ((show KFin.Vr i Dd from v) (K.H0.e0 (D := D) a))
      invFun := fun w => (show KFin.Vr i Dd from fun j => (eK (D.nbr i _ hn)).symm (w ((K.H0.e0 (D := D)).symm j)))
      map_add' := fun u v => funext fun a => map_add (eK (D.nbr i _ hn)) _ _
      map_smul' := fun c v => funext fun a => by
        show eK (D.nbr i _ hn) ((eK (D.nbr i _ hn)).symm c * (show KFin.Vr i Dd from v) (K.H0.e0 (D := D) a)) =
          c * eK (D.nbr i _ hn) ((show KFin.Vr i Dd from v) (K.H0.e0 (D := D) a))
        rw [map_mul, RingEquiv.apply_symm_apply]
      left_inv := fun v => funext fun j => by
        show (eK (D.nbr i _ hn)).symm (eK (D.nbr i _ hn)
          ((show KFin.Vr i Dd from v) (K.H0.e0 (D := D) ((K.H0.e0 (D := D)).symm j)))) = (show KFin.Vr i Dd from v) j
        rw [RingEquiv.symm_apply_apply, Equiv.apply_symm_apply]
      right_inv := fun w => funext fun a => by
        show eK (D.nbr i _ hn) ((eK (D.nbr i _ hn)).symm (w ((K.H0.e0 (D := D)).symm (K.H0.e0 (D := D) a)))) = w a
        rw [RingEquiv.apply_symm_apply, Equiv.symm_apply_apply] }
  refine ⟨F, fun g v => funext fun a => ?_⟩
  have h1 : F (repL (eK (D.nbr i _ hn)) (KFin.ρV i dc Dd l) (Br.iota D.nbr i _ hn) g v) a =
      eK (D.nbr i _ hn) (∑ j, Dd.ρk 0 (uElt Dd.r Dd.χ ((Br.iota D.nbr i _ hn g : KHf.Γn i dc (K.colIdx i dc l)) : GE D.nd))
        (K.H0.e0 (D := D) a) j • (show KFin.Vr i Dd from v) j) := rfl
  have h2 : KDim.repW i dc ρ π (K.colIdx i dc l) hn g (F v) a =
      ∑ b, algebraMap (Br.OLL D.nbr i _ hn) (Br.LL D.nbr i _ hn) ((D.nbr i _ hn).eO
        (WpO D.nd i ρ π ((Br.iota D.nbr i _ hn g : KHf.Γn i dc (K.colIdx i dc l)) : GE D.nd) a b)) * F v b := rfl

  rw [h1, h2, map_sum, ← Equiv.sum_comp (K.H0.e0 (D := D))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Algebra.smul_def, map_mul, KHf.eK_apply, Br.toLLK_alg, K.H0.unipotent_block_zero_entry hD hN _ a b]
  rfl

theorem rankFf_normAt (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (g0 : GE D.nd)
    (eB e₁ s : D.nd.X i → MatN D.nd i)
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (l : K.Col i dc) : KFin.RankFf i dc Dd ρ π l := by
  apply rankFf_iso (hD := hD) (hc := hc)
  exact isoV_of i dc Dd ρ π r g0 eB e₁ s hD hN l

end RecIso2

end Formalism.MainNotions.N.KTate
