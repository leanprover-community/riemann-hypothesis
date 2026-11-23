module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemImpAltAlt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigOfRatAd
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeAlgebraHasStableSublayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalGaloisPsiLevelAtPlace
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TransportAltAlt
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenCompatibleOfBadSet
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParLaws

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.GalLoc.EigLoc
end GlobalTheory.GalLoc.EigLoc
namespace GlobalTheory.GalLoc.EigLoc

theorem frobenius_eigenvalues_at_place_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c =>
    ∃ Sb : Finset (PlE c.a.nt.D.host), (∀ i, Sb ⊆ (withLoc c.a.nt.L).ntw.S0 i) ∧ (∀ Rw : RowSide (withLoc c.a.nt.L), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.TwInputs.EigTrue (withLoc c.a.nt.L) (cfL c.a.nt.L c.a.nt.cf) Rw Sb c.a.nt.eig) ∧ GlobalTheory.TwInputs.EigOcc (withLoc c.a.nt.L) ({ c.a.nt.S with } : RatDat (withLoc c.a.nt.L).ntw) c.a.nt.θ c.a.nt.hL Sb c.a.nt.eig := by
  intro hN hS hL
  have h2 : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c =>
    ∀ Sb : Finset (PlE (w.D Z).host), (∀ i, Sb ⊆ (w.D Z).ntw.S0 i) → ∃ Sb' : Finset (PlE (w.D Z).host), Sb ⊆ Sb' ∧
      (∀ i, Sb' ⊆ (w.D Z).ntw.S0 i) ∧ GlobalTheory.TwInputs.Eig.Low (w.D Z) Sb' ∧
      GlobalTheory.HeightCounting.RatSide.HeckeRd t.r.z.R t.r.z.cG c.row.kKs c.row.hk Sb' c.row.hecke.hL := _root_.GlobalTheory.T.exists_superset_low_heckeRd_of_subset_S0
  have h3 : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c =>
    ∃ θ : ∀ kk : Fin 2, Multiplicative (ZMod ((w.D Z).host.g kk)) →* (↥(w.D Z).LL0)ˣ, HEq θ c.a.nt.θ ∧
      GlobalTheory.HeightCounting.RatSide.LvlPsi t.r.z.R t.r.z.F t.r.z.cG θ := _root_.GlobalTheory.T.exists_theta_heq_lvlPsi_at_members
  refine _root_.GlobalTheory.GalLoc.atMem_mono (_root_.GlobalTheory.GalLoc.atMem_and' (h2 hN hS hL) (h3 hN hS hL)) ?_
  intro K B f T w Z Wt p0 t nch n xd c hE H
  obtain ⟨H2, H3⟩ := H
  obtain ⟨e⟩ := hE
  have e' : _root_.GlobalTheory.HeightCounting.RealExpansionExtraData (D := (w.st Z).toD7) c.row t.r.z.geo xd := e
  obtain ⟨Sb, eg, hSb, heq, hAd⟩ := e'.eig
  obtain ⟨Sb', hsub, hS0, hlow, hrd⟩ := H2 Sb hSb
  obtain ⟨θ, hθ, hψ⟩ := H3
  obtain ⟨Rw0, hRw0, ⟨hpar⟩⟩ := _root_.GlobalTheory.GalLoc.EigLoc.parIn_loc_alt c.a.nt _ c.row.rep_eq
  have hT := _root_.GlobalTheory.TwInputs.Eig.eigTrue_of_read hL t.r.Y t.r.z.pins.char.base.lev hpar.T Rw0 hpar.row hAd hsub hlow
  have hO := GlobalTheory.TwInputs.Eig.eigOcc t.r.Y t.r.z.pins.char.base.lev t.r.intersectionNumber_baseChange.prim.unif t.r.z.pins.char.base.models.HW
    t.r.z.good.2 hψ hAd hsub hlow hrd
  rw [t.r.z.lev.C] at hT
  exact _root_.GlobalTheory.GalLoc.EigLoc.transport_alt c.a.nt Sb' hS0 eg heq _ c.row.S_eq _ c.row.hL_eq θ hθ.symm Rw0 hRw0 hT hO
end GlobalTheory.GalLoc.EigLoc
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.eigTrue_and_eigOcc_withLoc : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c =>
    ∃ Sb : Finset (PlE c.a.nt.D.host), (∀ i, Sb ⊆ (withLoc c.a.nt.L).ntw.S0 i) ∧ (∀ Rw : RowSide (withLoc c.a.nt.L), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.TwInputs.EigTrue (withLoc c.a.nt.L) (cfL c.a.nt.L c.a.nt.cf) Rw Sb c.a.nt.eig) ∧ GlobalTheory.TwInputs.EigOcc (withLoc c.a.nt.L) ({ c.a.nt.S with } : RatDat (withLoc c.a.nt.L).ntw) c.a.nt.θ c.a.nt.hL Sb c.a.nt.eig := by
  first | exact @_root_.GlobalTheory.GalLoc.EigLoc.frobenius_eigenvalues_at_place_alt | exact _root_.GlobalTheory.GalLoc.EigLoc.frobenius_eigenvalues_at_place_alt | (intros; apply _root_.GlobalTheory.GalLoc.EigLoc.frobenius_eigenvalues_at_place_alt <;> assumption)
end
end
